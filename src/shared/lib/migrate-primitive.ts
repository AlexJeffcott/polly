/**
 * migrate-primitive — one-way cross-primitive data migration helper.
 *
 * Moving data from one Polly primitive to another ($sharedState to $peerState,
 * $peerState to $meshState, etc.) is a deliberate, one-time, application-authored
 * operation. The three primitive families serialise differently — LWW value plus
 * Lamport clock, plaintext Automerge ops, signed and encrypted Automerge ops —
 * and Polly never silently coerces between them. An application that wants to
 * move data explicitly reads the current value from the source, applies a
 * user-supplied transform, writes the result into the destination, and marks
 * the source as migrated so subsequent reads from it fail loudly rather than
 * returning stale data.
 *
 * This module provides the helper ({@link migratePrimitive}) and the migration
 * registry ({@link migrationRegistry}) that records which (key, primitive kind)
 * pairs have been migrated. Primitive read paths consult the registry at load
 * time and refuse to hydrate sources that have been marked. Migration is one-way
 * by design: there is no rollback, and running a migration twice throws.
 *
 * The registry is in-memory only. Persistence of the migrated flag across page
 * loads is each primitive's own responsibility at its storage boundary; Phase 1
 * and Phase 2 primitives will restore the registry state on startup from their
 * local stores.
 *
 * @example
 * ```ts
 * await migratePrimitive(
 *   $sharedState<OldNotes>("notes"),
 *   $meshState<NewNotes>("notes", { entries: [] }),
 *   (old) => ({ entries: old.entries ?? [] }),
 * );
 * ```
 */

import type { PrimitiveKind } from "./primitive-registry";

/**
 * Minimal interface that every migratable state primitive must satisfy. Real
 * primitive instances will implement this plus everything else their type
 * expects; tests construct plain objects.
 */
export interface MigratableState<T> {
  /** Stable logical key the primitive was registered under. */
  readonly key: string;
  /** The primitive kind owning this state. Used to identify entries in the
   * migration registry alongside the key. */
  readonly primitive: PrimitiveKind;
  /** Current value. Must be readable and writable. */
  value: T;
  /** Hydration promise. The migration helper awaits this on both source and
   * destination before reading the source value. */
  readonly loaded: Promise<void>;
}

/**
 * Error thrown by the migration subsystem. The {@link code} field distinguishes
 * the failure modes so callers can branch on them.
 */
export class MigrationError extends Error {
  readonly code: "already-migrated" | "same-primitive-instance";
  readonly key: string;
  readonly primitive: PrimitiveKind;

  constructor(
    message: string,
    code: MigrationError["code"],
    key: string,
    primitive: PrimitiveKind
  ) {
    super(message);
    this.name = "MigrationError";
    this.code = code;
    this.key = key;
    this.primitive = primitive;
  }
}

/**
 * In-memory registry of migrated (key, primitive kind) pairs. Exported as a
 * class so tests can construct fresh instances; application code uses the
 * module-level {@link migrationRegistry} singleton.
 */
export class MigrationRegistry {
  private readonly marks = new Set<string>();

  private entryKey(key: string, primitive: PrimitiveKind): string {
    return `${primitive}:${key}`;
  }

  /** Mark a source primitive as migrated. Idempotent. */
  mark(key: string, primitive: PrimitiveKind): void {
    this.marks.add(this.entryKey(key, primitive));
  }

  /** Check whether a source primitive has been marked as migrated. */
  isMarked(key: string, primitive: PrimitiveKind): boolean {
    return this.marks.has(this.entryKey(key, primitive));
  }

  /** Drop every mark. Intended for tests; application code should not call this. */
  clear(): void {
    this.marks.clear();
  }

  /** Number of recorded marks. Intended for tests. */
  get size(): number {
    return this.marks.size;
  }
}

/**
 * The process-wide migration registry. Primitives and application migrations
 * both consult it: tests can reset it with {@link MigrationRegistry.clear}.
 */
export const migrationRegistry = new MigrationRegistry();

/**
 * Migrate data from one Polly primitive to another. Reads the source's current
 * value, applies the caller's transform, writes the result to the destination,
 * and marks the source as migrated so subsequent reads fail loudly.
 *
 * The helper is one-way and one-time. Running it twice on the same source
 * throws a {@link MigrationError} with code `already-migrated`. Running it
 * with the same object as both source and destination throws with code
 * `same-primitive-instance`.
 *
 * Applications invoke this explicitly on upgrade, once per device, typically
 * inside a startup hook before the primitives that depend on the migrated data
 * are read. It is not a replacement for the schema-version migration protocol
 * inside a single primitive — that handles shape evolution within one primitive
 * family, whereas this helper handles moves between primitive families.
 */
export async function migratePrimitive<Source, Destination>(
  source: MigratableState<Source>,
  destination: MigratableState<Destination>,
  transform: (value: Source) => Destination
): Promise<void> {
  if ((source as unknown) === (destination as unknown)) {
    throw new MigrationError(
      `Cannot migrate a primitive to itself: "${source.key}" under ${source.primitive}.`,
      "same-primitive-instance",
      source.key,
      source.primitive
    );
  }
  if (migrationRegistry.isMarked(source.key, source.primitive)) {
    throw new MigrationError(
      `Cannot migrate: source "${source.key}" under $${source.primitive} has already been migrated. Migrations are one-way and one-time.`,
      "already-migrated",
      source.key,
      source.primitive
    );
  }
  await source.loaded;
  await destination.loaded;
  const transformed = transform(source.value);
  destination.value = transformed;
  migrationRegistry.mark(source.key, source.primitive);
}
