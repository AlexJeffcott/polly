/**
 * schema-version — plumbing for the shared schema-version migration protocol
 * used by $peerState and $meshState documents.
 *
 * Every peer-first document carries a reserved schema-version field. When a
 * client loads a document whose stored version is lower than the application's
 * declared target version, Polly walks the registered migrations in sequence,
 * mutating the document from one version to the next, and stamps the new
 * version on the way through. When the stored version is higher, Polly refuses
 * to load and surfaces a structured error: the application is older than the
 * document and should be upgraded.
 *
 * For concurrent writes across mixed client versions, every op also carries
 * the schema version under which it was produced. Ops whose version is lower
 * than the document's current version are rejected at sync time; the peer
 * producing them needs to upgrade its local replica through the migration
 * runner before retrying. Ops whose version is higher mean the current peer
 * is behind the application that produced them; rejecting them prevents
 * corruption while still surfacing the mismatch to the user.
 *
 * This module provides only the plumbing — the reserved field name, the
 * reader and writer for the version field, the migration runner, and the
 * op-version compatibility check. Phase 1 and Phase 2 primitives will consume
 * these helpers; nothing in this file depends on Automerge or any transport.
 */

/**
 * The reserved field name used to store the schema version on every peer-first
 * document. Applications must not use this field for their own data; the
 * primitive constructors reserve it at the document boundary.
 */
export const SCHEMA_VERSION_FIELD = "__schemaVersion" as const;

/**
 * The minimal shape every peer-first document satisfies. Applications layer
 * their own fields on top of this; the reserved {@link SCHEMA_VERSION_FIELD}
 * is the only required key.
 */
export type VersionedDoc = {
  [SCHEMA_VERSION_FIELD]?: number;
  [otherField: string]: unknown;
};

/**
 * A single migration step. Mutates the document in place, transforming it
 * from version (target - 1) to version target. The implementation must be
 * total (accept any valid v(target-1) document) and deterministic (running
 * it twice produces the same result). Applications that want return-a-new-doc
 * semantics should copy inside the migration body rather than returning.
 */
export type Migration = (doc: Record<string, unknown>) => void;

/**
 * A map from target schema version to the migration that produces it. The
 * keys must be contiguous from 1 upward through the application's target
 * version, with no gaps. Gaps throw at migration time.
 *
 * @example
 * ```ts
 * const migrations: Migrations = {
 *   1: (doc) => { doc["title"] = ""; },                    // v0 → v1
 *   2: (doc) => { doc["tags"] = []; },                     // v1 → v2
 *   3: (doc) => { doc["archived"] = false; delete doc["deleted"]; }, // v2 → v3
 * };
 * ```
 */
export type Migrations = Record<number, Migration>;

/**
 * Error thrown by the schema-version subsystem. The `code` field distinguishes
 * the failure modes so that callers (primitive constructors, application error
 * handlers) can decide whether to surface the error to the user, prompt an
 * upgrade, or drop the offending op.
 */
export class SchemaVersionError extends Error {
  readonly code:
    | "doc-ahead-of-app"
    | "missing-migration"
    | "op-older-than-doc"
    | "op-newer-than-doc";
  readonly docVersion?: number;
  readonly targetVersion?: number;
  readonly opVersion?: number;
  readonly missingVersion?: number;

  constructor(
    message: string,
    code: SchemaVersionError["code"],
    details: {
      docVersion?: number;
      targetVersion?: number;
      opVersion?: number;
      missingVersion?: number;
    } = {}
  ) {
    super(message);
    this.name = "SchemaVersionError";
    this.code = code;
    if (details.docVersion !== undefined) this.docVersion = details.docVersion;
    if (details.targetVersion !== undefined) this.targetVersion = details.targetVersion;
    if (details.opVersion !== undefined) this.opVersion = details.opVersion;
    if (details.missingVersion !== undefined) this.missingVersion = details.missingVersion;
  }
}

/**
 * Read the schema version stored on a document. Returns 0 for documents that
 * have never been stamped (undefined field), which is the canonical "pre-v1"
 * sentinel — the first migration in a registry is always keyed at 1 and
 * handles the undefined-to-1 transition.
 */
export function getDocVersion(doc: unknown): number {
  if (typeof doc !== "object" || doc === null) return 0;
  const record = doc as Record<string, unknown>;
  const value = record[SCHEMA_VERSION_FIELD];
  return typeof value === "number" && Number.isInteger(value) && value >= 0 ? value : 0;
}

/**
 * Stamp a schema version onto a document in place. Primitive constructors call
 * this after each migration step and once on document creation.
 */
export function setDocVersion(doc: Record<string, unknown>, version: number): void {
  doc[SCHEMA_VERSION_FIELD] = version;
}

/**
 * Run any pending migrations on a document. Mutates the document in place.
 *
 * @throws {SchemaVersionError} with code `doc-ahead-of-app` if the document is
 *   already at a version higher than the application's target.
 * @throws {SchemaVersionError} with code `missing-migration` if an intermediate
 *   migration is missing from the registry.
 */
export function runMigrations(
  doc: Record<string, unknown>,
  targetVersion: number,
  migrations: Migrations
): void {
  const current = getDocVersion(doc);
  if (current > targetVersion) {
    throw new SchemaVersionError(
      `Document is at schema version ${current} but the application targets ${targetVersion}. Upgrade the application to continue.`,
      "doc-ahead-of-app",
      { docVersion: current, targetVersion }
    );
  }
  for (let v = current + 1; v <= targetVersion; v++) {
    const migration = migrations[v];
    if (!migration) {
      throw new SchemaVersionError(
        `Missing migration for schema version ${v}. Migrations must be contiguous from ${current + 1} through ${targetVersion}.`,
        "missing-migration",
        { docVersion: current, targetVersion, missingVersion: v }
      );
    }
    migration(doc);
    setDocVersion(doc, v);
  }
}

/**
 * Result of an op-version compatibility check. Discriminated by the {@link compatible}
 * field so callers can switch cleanly.
 */
export type OpVersionCheck =
  | { compatible: true }
  | {
      compatible: false;
      reason: "op-older-than-doc" | "op-newer-than-doc";
      opVersion: number;
      docVersion: number;
    };

/**
 * Check whether an incoming op's declared schema version is compatible with
 * the document's current version. Ops that match are applied; ops that are
 * older are rejected (the producing peer is behind and should migrate); ops
 * that are newer are also rejected (the current peer is behind and should
 * upgrade).
 */
export function checkOpVersion(opVersion: number, docVersion: number): OpVersionCheck {
  if (opVersion < docVersion) {
    return { compatible: false, reason: "op-older-than-doc", opVersion, docVersion };
  }
  if (opVersion > docVersion) {
    return { compatible: false, reason: "op-newer-than-doc", opVersion, docVersion };
  }
  return { compatible: true };
}

/**
 * Convenience wrapper around {@link checkOpVersion} that throws a structured
 * {@link SchemaVersionError} on incompatibility. Useful inside sync handlers
 * that want to surface the mismatch through their normal error pipeline.
 */
export function assertOpVersion(opVersion: number, docVersion: number): void {
  const result = checkOpVersion(opVersion, docVersion);
  if (result.compatible) return;
  const message =
    result.reason === "op-older-than-doc"
      ? `Incoming op was produced at schema version ${opVersion} but the document is at version ${docVersion}. The producing peer is behind.`
      : `Incoming op was produced at schema version ${opVersion} but the document is at version ${docVersion}. The current peer is behind and should upgrade.`;
  throw new SchemaVersionError(message, result.reason, { opVersion, docVersion });
}
