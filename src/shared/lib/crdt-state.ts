/**
 * crdt-state — base machinery for Polly's peer-first state primitives.
 *
 * This module is transport-agnostic: it takes a caller-supplied async factory
 * that produces a ready {@link DocHandle}, binds it bidirectionally to a
 * Preact signal, runs any pending schema migrations on load, and integrates
 * with the primitive-registry and migration-registry guards. Phase 1's
 * $peerState and Phase 2's $meshState both construct these base primitives
 * with their own handle factories — one over Automerge-Repo's WebSocket
 * client adapter, the other over WebRTC — and the base never knows which.
 *
 * The signal-to-handle binding uses an `updating` guard flag to prevent write
 * loops: when a local signal assignment runs the effect that pushes the value
 * into `handle.change`, the flag is raised so that the 'change' event the
 * handle fires back is ignored. The same flag protects in the other direction
 * when a remote change seeds the signal.
 *
 * For the Phase 0 cut, writes are applied with a naive top-level structural
 * replacement inside the `Automerge.change` block. This is correct for
 * JSON-shaped documents with scalar and flat-object fields and is good enough
 * to exercise the rest of the pipeline. The specialised variants for text,
 * counters, and lists (which require type-specific operation capture to
 * preserve concurrent-edit semantics) land in Phase 1's crdt-specialised.ts.
 */

import type { DocHandle } from "@automerge/automerge-repo";
import { effect, signal } from "@preact/signals";
import type { Access } from "./access";
import { type MigratableState, MigrationError, migrationRegistry } from "./migrate-primitive";
import { type PrimitiveKind, primitiveRegistry } from "./primitive-registry";
import {
  type Migrations,
  runMigrations,
  SCHEMA_VERSION_FIELD,
  setDocVersion,
  type VersionedDoc,
} from "./schema-version";

/**
 * The interface a Polly peer-first primitive exposes at the call site. It
 * satisfies {@link MigratableState} so that the cross-primitive migration
 * helper can consume it directly.
 */
export interface CrdtPrimitive<T extends VersionedDoc> extends MigratableState<T> {
  /** Stable logical key the primitive was registered under. */
  readonly key: string;
  /** Primitive kind — one of the {@link PrimitiveKind} labels. */
  readonly primitive: PrimitiveKind;
  /** Current value. Writes push into the backing Automerge document. */
  value: T;
  /** Resolves when the handle is ready and migrations have run. */
  readonly loaded: Promise<void>;
  /** The underlying {@link DocHandle}, populated after {@link loaded} resolves.
   * Intended for advanced escape hatches; most callers should stay at the
   * signal surface. */
  readonly handle: DocHandle<T> | undefined;
}

/**
 * Options for constructing a base CRDT-backed primitive. Phase 1 and Phase 2
 * primitive constructors pass a transport-specific {@link getHandle} factory
 * and their own {@link primitive} label; everything else is shared.
 */
export interface CrdtStateOptions<T extends VersionedDoc> {
  /** Stable logical key identifying this piece of state. */
  key: string;
  /** Primitive kind label for registry and error-message purposes. */
  primitive: PrimitiveKind;
  /** Initial value if no stored document exists yet. Applied by the caller's
   * handle factory; the base module does not create documents itself. */
  initialValue: T;
  /** Async factory that resolves to a ready {@link DocHandle}. The factory is
   * responsible for repo lookup, document creation, and any transport-specific
   * setup. The base module calls this once, during hydration. */
  getHandle: () => Promise<DocHandle<T>>;
  /** Target schema version for the application. If set, migrations run on
   * load to bring the document up to this version before the signal hydrates. */
  schemaVersion?: number;
  /** Migration table. Ignored if {@link schemaVersion} is not set. */
  migrations?: Migrations;
  /** Declarative access predicates. Not consumed by the base module; the
   * transport-specific constructors compile it to their enforcement layer. */
  access?: Access;
  /** Optional free-text call-site label for primitive-registry error messages. */
  callSite?: string;
}

/**
 * Construct a base CRDT-backed Polly primitive. Integrates with
 * primitive-registry (for collision detection), migration-registry (for
 * cross-family migration guards), and schema-version (for on-load migrations).
 *
 * @throws {MigrationError} if the source key has been marked as migrated.
 * @throws {PrimitiveCollisionError} if the key is already registered under a
 *   different primitive kind.
 */
export function $crdtState<T extends VersionedDoc>(options: CrdtStateOptions<T>): CrdtPrimitive<T> {
  if (migrationRegistry.isMarked(options.key, options.primitive)) {
    throw new MigrationError(
      `Cannot construct $${options.primitive}("${options.key}"): this key has been marked as migrated. Migrations are one-way; use the destination primitive instead.`,
      "already-migrated",
      options.key,
      options.primitive
    );
  }
  primitiveRegistry.register(options.key, options.primitive, options.callSite);

  const inner = signal<T>(options.initialValue);
  let updating = false;
  let currentHandle: DocHandle<T> | undefined;

  const loaded = (async () => {
    const handle = await options.getHandle();
    await handle.whenReady();
    currentHandle = handle;

    // Run any pending schema migrations inside a change block so they land
    // as a single Automerge operation set.
    if (options.schemaVersion !== undefined) {
      const targetVersion = options.schemaVersion;
      const migrations = options.migrations ?? {};
      handle.change((doc) => {
        runMigrations(doc as Record<string, unknown>, targetVersion, migrations);
        // runMigrations stamps the version on every intermediate step; make
        // sure the final value is recorded even when no migrations ran.
        setDocVersion(doc as Record<string, unknown>, targetVersion);
      });
    }

    // Seed the signal with the hydrated doc state. Raise the guard first so
    // the 'change' listener we install below does not echo this write back.
    updating = true;
    try {
      inner.value = cloneDoc(handle.doc());
    } finally {
      updating = false;
    }

    // Remote-changes-to-signal binding.
    handle.on("change", (payload) => {
      if (updating) return;
      updating = true;
      try {
        inner.value = cloneDoc(payload.doc);
      } finally {
        updating = false;
      }
    });

    // Signal-to-remote binding. The effect runs once on registration with
    // the already-hydrated value; the guard makes that first run a no-op at
    // the handle level because updating is false but the doc already equals
    // the signal, so Automerge records no new operations.
    effect(() => {
      const value = inner.value;
      if (updating) return;
      if (!currentHandle) return;
      updating = true;
      try {
        currentHandle.change((doc) => {
          applyTopLevel(doc as Record<string, unknown>, value);
        });
      } finally {
        updating = false;
      }
    });
  })();

  return {
    key: options.key,
    primitive: options.primitive,
    get value() {
      return inner.value;
    },
    set value(next: T) {
      inner.value = next;
    },
    loaded,
    get handle() {
      return currentHandle;
    },
  };
}

/**
 * Shallow clone of an Automerge doc into a plain JS object. Automerge docs
 * are Proxies; the signal holds a detached plain-object snapshot so that
 * application code does not accidentally mutate the CRDT through the signal.
 */
function cloneDoc<T>(doc: T): T {
  return JSON.parse(JSON.stringify(doc)) as T;
}

/**
 * Copy every top-level field from the incoming value onto the Automerge doc.
 * This is the naive Phase 0 write path: correct for flat JSON-shaped documents
 * and good enough for the base module's tests. Specialised primitives in
 * Phase 1 will replace this with type-aware operation capture for text,
 * counters, and lists.
 *
 * The reserved schema-version field is not copied — it is managed by the
 * migration subsystem and must not be overwritten by application writes.
 */
function applyTopLevel<T extends VersionedDoc>(doc: Record<string, unknown>, value: T): void {
  for (const key of Object.keys(value)) {
    if (key === SCHEMA_VERSION_FIELD) continue;
    doc[key] = (value as Record<string, unknown>)[key];
  }
}
