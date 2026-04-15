/**
 * crdt-specialised — text, counter, and list variants for Polly's peer-first
 * state primitives.
 *
 * Where the base $crdtState binds a signal to a whole Automerge document with
 * naive top-level structural assignment, the specialised variants each own a
 * single field inside their document and use type-specific Automerge
 * operations to mutate it. This is the difference between "your write
 * survives a concurrent edit" and "your write clobbers the other peer's
 * edit," and it matters most for text editing where every keystroke from a
 * concurrent peer would otherwise be lost.
 *
 * - **$crdtText** stores its value in `doc.text` and writes via
 *   `Automerge.updateText`, which computes the minimal sequence of character
 *   splices between the previous and new strings and records each one as a
 *   CRDT operation. Concurrent text edits merge.
 *
 * - **$crdtCounter** stores its value in `doc.count` as an `Automerge.Counter`
 *   instance and writes via `counter.increment(delta)`. Increments commute
 *   across peers, so two clients each adding 1 to a counter at 5 produce a
 *   counter at 7 after merging — last-write-wins semantics on a plain number
 *   would lose one of the increments.
 *
 * - **$crdtList** stores its value in `doc.items` and, for the Phase 0 cut,
 *   uses naive whole-array replacement on every write. This is correct for
 *   single-writer scenarios and good enough to exercise the rest of the
 *   pipeline. Phase 1 will replace the write path with proper diff-to-splice
 *   logic so that concurrent inserts and removes preserve list ordering.
 *
 * All three variants share a single internal factory that handles the
 * primitive-registry guard, migration-registry guard, schema-version
 * migration, hydration promise, two-way binding with an `updating` flag,
 * and the {@link MigratableState} interface. Variants differ only in the
 * `extractValue` and `applyWrite` hooks they pass.
 */

import { Counter, type DocHandle, updateText } from "@automerge/automerge-repo";
import { effect, signal } from "@preact/signals";
import type { Access } from "./access";
import { type MigratableState, MigrationError, migrationRegistry } from "./migrate-primitive";
import { type PrimitiveKind, primitiveRegistry } from "./primitive-registry";
import { type Migrations, runMigrations, setDocVersion, type VersionedDoc } from "./schema-version";

/**
 * Public interface for a specialised primitive. The signal value type V is
 * not the same as the underlying Automerge document — for example, $crdtText
 * exposes a string signal whose value lives at `doc.text` inside the
 * document. Implements {@link MigratableState} so the cross-primitive
 * migration helper can consume it directly.
 */
export interface SpecialisedPrimitive<V> extends MigratableState<V> {
  readonly key: string;
  readonly primitive: PrimitiveKind;
  value: V;
  readonly loaded: Promise<void>;
  readonly handle: DocHandle<unknown> | undefined;
}

/** Internal config shape consumed by {@link createSpecialisedPrimitive}. */
interface SpecialisedConfig<V, D extends VersionedDoc> {
  key: string;
  primitive: PrimitiveKind;
  initialValue: V;
  getHandle: () => Promise<DocHandle<D>>;
  /** Read the typed signal value out of the Automerge document. Called once
   * on hydration and again on every remote change. */
  extractValue: (doc: D) => V;
  /** Apply a typed signal value to the Automerge document inside the
   * `handle.change` block. Called every time the local signal is reassigned. */
  applyWrite: (doc: D, value: V) => void;
  schemaVersion?: number;
  migrations?: Migrations;
  access?: Access;
  callSite?: string;
}

/**
 * Shared factory. Identical guard, hydration, and binding wiring across all
 * three specialised variants; the variants differ only in the extract and
 * apply hooks they supply.
 */
function createSpecialisedPrimitive<V, D extends VersionedDoc>(
  config: SpecialisedConfig<V, D>
): SpecialisedPrimitive<V> {
  if (migrationRegistry.isMarked(config.key, config.primitive)) {
    throw new MigrationError(
      `Cannot construct $${config.primitive}("${config.key}"): this key has been marked as migrated. Migrations are one-way; use the destination primitive instead.`,
      "already-migrated",
      config.key,
      config.primitive
    );
  }
  primitiveRegistry.register(config.key, config.primitive, config.callSite);

  const inner = signal<V>(config.initialValue);
  let updating = false;
  let currentHandle: DocHandle<D> | undefined;

  const loaded = (async () => {
    const handle = await config.getHandle();
    await handle.whenReady();
    currentHandle = handle;

    if (config.schemaVersion !== undefined) {
      const targetVersion = config.schemaVersion;
      const migrations = config.migrations ?? {};
      handle.change((doc) => {
        runMigrations(doc as Record<string, unknown>, targetVersion, migrations);
        setDocVersion(doc as Record<string, unknown>, targetVersion);
      });
    }

    updating = true;
    try {
      inner.value = config.extractValue(handle.doc());
    } finally {
      updating = false;
    }

    handle.on("change", (payload) => {
      if (updating) return;
      updating = true;
      try {
        inner.value = config.extractValue(payload.doc);
      } finally {
        updating = false;
      }
    });

    effect(() => {
      const value = inner.value;
      if (updating) return;
      if (!currentHandle) return;
      updating = true;
      try {
        currentHandle.change((doc) => {
          config.applyWrite(doc, value);
        });
      } finally {
        updating = false;
      }
    });
  })();

  return {
    key: config.key,
    primitive: config.primitive,
    get value() {
      return inner.value;
    },
    set value(next: V) {
      inner.value = next;
    },
    loaded,
    get handle() {
      return currentHandle as DocHandle<unknown> | undefined;
    },
  };
}

// ─── $crdtText ──────────────────────────────────────────────────────────────

/** The Automerge document shape backing a $crdtText primitive. */
export type TextDoc = VersionedDoc & { text?: string };

/** Options for {@link $crdtText}. */
export interface CrdtTextOptions {
  /** Primitive kind label. Defaults to "peerState"; Phase 2's $meshState
   * wrapper passes "meshState" instead. */
  primitive?: PrimitiveKind;
  /** Async factory that returns a ready DocHandle for the text document. */
  getHandle: () => Promise<DocHandle<TextDoc>>;
  schemaVersion?: number;
  migrations?: Migrations;
  access?: Access;
  callSite?: string;
}

/**
 * Create a CRDT-backed text primitive. The signal exposes a plain string;
 * writes are diffed into character-level splices via `Automerge.updateText`
 * so that concurrent edits from peers merge cleanly rather than clobbering
 * each other.
 */
export function $crdtText(
  key: string,
  initialValue: string,
  options: CrdtTextOptions
): SpecialisedPrimitive<string> {
  return createSpecialisedPrimitive<string, TextDoc>({
    key,
    primitive: options.primitive ?? "peerState",
    initialValue,
    getHandle: options.getHandle,
    extractValue: (doc) => doc.text ?? "",
    applyWrite: (doc, value) => {
      if (doc.text === undefined) {
        // First write — seed the field. Subsequent writes will use updateText.
        (doc as TextDoc).text = value;
      } else {
        updateText(doc, ["text"], value);
      }
    },
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
    callSite: options.callSite,
  });
}

// ─── $crdtCounter ───────────────────────────────────────────────────────────

/** The Automerge document shape backing a $crdtCounter primitive. */
export type CounterDoc = VersionedDoc & { count?: Counter };

/** Options for {@link $crdtCounter}. */
export interface CrdtCounterOptions {
  primitive?: PrimitiveKind;
  getHandle: () => Promise<DocHandle<CounterDoc>>;
  schemaVersion?: number;
  migrations?: Migrations;
  access?: Access;
  callSite?: string;
}

/**
 * Create a CRDT-backed counter primitive. The signal exposes a plain number;
 * writes compute the delta from the document's current value and call
 * `counter.increment(delta)` on the underlying `Automerge.Counter`. Concurrent
 * increments from peers commute, so two clients each adding 1 to a counter at
 * 5 produce a counter at 7 after merging.
 *
 * Application code that wants to express increments idiomatically can write
 * `counter.value = counter.value + 1`; the signal's reactivity captures the
 * read-then-write pattern and the factory translates it into a proper CRDT
 * increment operation underneath.
 */
export function $crdtCounter(
  key: string,
  initialValue: number,
  options: CrdtCounterOptions
): SpecialisedPrimitive<number> {
  return createSpecialisedPrimitive<number, CounterDoc>({
    key,
    primitive: options.primitive ?? "peerState",
    initialValue,
    getHandle: options.getHandle,
    extractValue: (doc) => {
      const c = doc.count;
      if (c === undefined) return 0;
      return c.value;
    },
    applyWrite: (doc, value) => {
      const existing = doc.count;
      if (existing === undefined) {
        (doc as CounterDoc).count = new Counter(value);
      } else {
        const delta = value - existing.value;
        if (delta !== 0) {
          existing.increment(delta);
        }
      }
    },
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
    callSite: options.callSite,
  });
}

// ─── $crdtList ──────────────────────────────────────────────────────────────

/** The Automerge document shape backing a $crdtList primitive. */
export type ListDoc<T> = VersionedDoc & { items?: T[] };

/** Options for {@link $crdtList}. */
export interface CrdtListOptions<T> {
  primitive?: PrimitiveKind;
  getHandle: () => Promise<DocHandle<ListDoc<T>>>;
  schemaVersion?: number;
  migrations?: Migrations;
  access?: Access;
  callSite?: string;
}

/**
 * Create a CRDT-backed list primitive. The signal exposes a plain array;
 * for the Phase 0 cut, writes replace the underlying array wholesale inside
 * an `Automerge.change` block. This is correct for single-writer scenarios
 * and is the simplest way to ship a working list primitive on the same
 * pipeline as text and counter.
 *
 * Phase 1 will replace the write path with proper structural diffing into
 * insert and remove operations so that concurrent edits from peers preserve
 * list ordering. Until then, applications using $crdtList in a multi-writer
 * setting should expect last-writer-wins semantics on the array as a whole.
 */
export function $crdtList<T>(
  key: string,
  initialValue: T[],
  options: CrdtListOptions<T>
): SpecialisedPrimitive<T[]> {
  return createSpecialisedPrimitive<T[], ListDoc<T>>({
    key,
    primitive: options.primitive ?? "peerState",
    initialValue,
    getHandle: options.getHandle,
    extractValue: (doc) => (doc.items ? [...doc.items] : []),
    applyWrite: (doc, value) => {
      // Phase 0 naive replacement; see the function-level docstring for the
      // refinement plan.
      (doc as ListDoc<T>).items = [...value];
    },
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
    callSite: options.callSite,
  });
}
