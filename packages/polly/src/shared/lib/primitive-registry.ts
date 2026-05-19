/**
 * PrimitiveRegistry — runtime namespace collision detection across Polly's
 * synced state primitives.
 *
 * The three primitive families ($sharedState, $peerState, $meshState) each store
 * data under a developer-chosen logical key. If two different primitives both
 * claim the same key, the developer almost certainly has a bug: the on-disk
 * formats are incompatible, no sync happens between them, and whichever primitive
 * resolves first silently "wins" from the developer's perspective. By the time
 * the mistake is noticed, data has diverged.
 *
 * The registry catches the mistake at the first mismatched registration and
 * throws a structured error naming the key, both primitives, and (when available)
 * the call site of each registration. This is run-to-failure by design: a
 * collision is always a bug, and the failure should be loud.
 *
 * Same primitive re-registering the same key is allowed and is a no-op — it
 * supports hot module reloading and component re-mounts without spurious errors.
 * Changing the primitive kind of an existing key is still an error; developers
 * doing that during local HMR should hard-reload to reset the registry.
 *
 * @example
 * ```ts
 * primitiveRegistry.register("notes", "sharedState", "src/app.ts:10");
 * primitiveRegistry.register("notes", "peerState", "src/other.ts:22");
 * // throws PrimitiveCollisionError — names both primitives and both call sites
 * ```
 */

/**
 * Canonical identifiers for Polly's synced state primitives. The registry
 * uses these as opaque labels; nothing else in Polly needs to match them.
 */
export type PrimitiveKind =
  | "sharedState"
  | "syncedState"
  | "persistedState"
  | "state"
  | "peerState"
  | "meshState";

/**
 * Thrown when a logical key is registered under more than one primitive.
 * The message names the key, both primitives, and (when available) the
 * call site of each registration, so the developer can navigate to both
 * sites from the error output.
 */
export class PrimitiveCollisionError extends Error {
  readonly key: string;
  readonly firstPrimitive: PrimitiveKind;
  readonly firstCallSite: string | undefined;
  readonly secondPrimitive: PrimitiveKind;
  readonly secondCallSite: string | undefined;

  constructor(
    key: string,
    firstPrimitive: PrimitiveKind,
    firstCallSite: string | undefined,
    secondPrimitive: PrimitiveKind,
    secondCallSite: string | undefined
  ) {
    const firstLocation = firstCallSite ? ` (at ${firstCallSite})` : "";
    const secondLocation = secondCallSite ? ` (at ${secondCallSite})` : "";
    super(
      `Polly primitive key collision: "${key}" is already registered as ` +
        `$${firstPrimitive}${firstLocation} and cannot also be registered ` +
        `as $${secondPrimitive}${secondLocation}. Pick a different key or ` +
        `use the same primitive in both places.`
    );
    this.name = "PrimitiveCollisionError";
    this.key = key;
    this.firstPrimitive = firstPrimitive;
    this.firstCallSite = firstCallSite;
    this.secondPrimitive = secondPrimitive;
    this.secondCallSite = secondCallSite;
  }
}

type RegistryEntry = {
  primitive: PrimitiveKind;
  callSite: string | undefined;
};

/**
 * A small Map-backed registry of "logical key → primitive kind". Exported as
 * a class so tests can construct fresh instances without sharing state; the
 * module-level {@link primitiveRegistry} singleton is what application code
 * actually uses.
 */
export class PrimitiveRegistry {
  private readonly entries = new Map<string, RegistryEntry>();

  /**
   * Register a key under a primitive kind. Re-registering the same key under
   * the same primitive is a no-op, which is what hot module reloading and
   * component re-mounts produce.
   *
   * @throws {PrimitiveCollisionError} if the key is already registered under
   *   a different primitive kind.
   */
  register(key: string, primitive: PrimitiveKind, callSite?: string): void {
    const existing = this.entries.get(key);
    if (existing && existing.primitive !== primitive) {
      throw new PrimitiveCollisionError(
        key,
        existing.primitive,
        existing.callSite,
        primitive,
        callSite
      );
    }
    if (!existing) {
      this.entries.set(key, { primitive, callSite });
    }
  }

  /**
   * True if the key has been registered (under any primitive kind).
   */
  has(key: string): boolean {
    return this.entries.has(key);
  }

  /**
   * Look up the primitive kind a key is registered under, if any.
   * Returns undefined for unregistered keys.
   */
  kindOf(key: string): PrimitiveKind | undefined {
    return this.entries.get(key)?.primitive;
  }

  /**
   * Drop every registration. Intended for test setup and teardown; application
   * code should not call this.
   */
  clear(): void {
    this.entries.clear();
  }

  /**
   * Number of registered keys. Intended for tests.
   */
  get size(): number {
    return this.entries.size;
  }
}

/**
 * The process-wide primitive registry. Application code registers here
 * implicitly via primitive constructors; tests can reset it with `clear()`.
 */
export const primitiveRegistry = new PrimitiveRegistry();
