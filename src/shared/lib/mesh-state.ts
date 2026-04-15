/**
 * mesh-state — Phase 2 wrappers exposing $meshState, $meshText, $meshCounter,
 * and $meshList. These are the application-facing constructors for the
 * strongest resilience tier in RFC-041: every device is a full Automerge
 * replica, the server is *not on the data path at all*, and the application
 * functions with zero server uptime once direct peer connections are
 * established.
 *
 * Each primitive wraps the corresponding Phase 0 base ($crdtState, $crdtText,
 * $crdtCounter, $crdtList) with three additions:
 *
 *   1. The `primitive` label is hard-coded to "meshState" so the
 *      primitive-registry collision detection knows which family the key
 *      belongs to.
 *
 *   2. A handle factory that resolves the application's logical key to an
 *      Automerge DocumentId via a per-Repo key map, identical in shape to
 *      the $peerState factory but registered against a separate Repo
 *      configured for the mesh transport (signed and encrypted at the
 *      network layer).
 *
 *   3. Signing and encryption are mandatory, not optional. Where $peerState
 *      accepts encrypt/sign as opt-in flags (currently throwing in Phase 1),
 *      $meshState requires every operation to be signed by the originating
 *      peer's key and encrypted under the document's symmetric key. The
 *      mechanism lives in the wrapping MeshNetworkAdapter that the Repo
 *      uses for transport.
 *
 * The Repo itself is supplied by the application via {@link configureMeshState}
 * or per-call via the `repo` option. In Phase 2 the production transport will
 * be a WebRTC mesh adapter wrapping signing+encryption around an in-process
 * RTCDataChannel; for tests and for the early Phase 2 cut, an in-memory
 * loopback adapter pair satisfies the same contract.
 */

import type { DocHandle, DocumentId, Repo } from "@automerge/automerge-repo";
import type { Access } from "./access";
import {
  $crdtCounter,
  $crdtList,
  $crdtText,
  type CounterDoc,
  type ListDoc,
  type SpecialisedPrimitive,
  type TextDoc,
} from "./crdt-specialised";
import { $crdtState, type CrdtPrimitive } from "./crdt-state";
import type { Migrations, VersionedDoc } from "./schema-version";

/** Common option shape across all four $mesh* primitives. */
export interface MeshStateOptions {
  /** Override the default Repo for this primitive. The Repo must be
   * configured with the mesh transport (signing and encryption at the
   * network layer). */
  repo?: Repo;
  /** Schema version target for the application. Migrations run on load. */
  schemaVersion?: number;
  /** Migration table keyed by target version. Required if schemaVersion is set. */
  migrations?: Migrations;
  /** Declarative read/write access. The mesh transport compiles this into
   * a public-key set used by the signing layer to verify incoming ops. */
  access?: Access;
}

/** Internal: per-Repo key → DocumentId map. */
const keyMapsByRepo = new WeakMap<Repo, Map<string, DocumentId>>();
let defaultRepo: Repo | undefined;

/**
 * Set the default Repo that the $mesh* primitives use when no `repo` option
 * is supplied. Calling this with a new Repo clears the per-Repo key map so
 * that tests start each scenario with a fresh document space.
 *
 * Production code typically calls this once at application startup with a
 * Repo configured for the mesh transport. Tests call it before each
 * scenario with an in-memory or loopback Repo.
 */
export function configureMeshState(repo: Repo): void {
  defaultRepo = repo;
  keyMapsByRepo.set(repo, new Map());
}

/**
 * Reset the mesh-state subsystem to its initial unconfigured state.
 * Intended for tests; production code should not call this.
 */
export function resetMeshState(): void {
  defaultRepo = undefined;
}

function resolveRepo(option: Repo | undefined): Repo {
  const repo = option ?? defaultRepo;
  if (!repo) {
    throw new Error(
      "Polly $meshState: no Repo configured. Call configureMeshState(repo) at startup or pass { repo } in the primitive options."
    );
  }
  return repo;
}

function getKeyMap(repo: Repo): Map<string, DocumentId> {
  let map = keyMapsByRepo.get(repo);
  if (!map) {
    map = new Map();
    keyMapsByRepo.set(repo, map);
  }
  return map;
}

function buildHandleFactory<D>(
  repo: Repo,
  key: string,
  initialDoc: D
): () => Promise<DocHandle<D>> {
  return async () => {
    const map = getKeyMap(repo);
    const existingId = map.get(key);
    if (existingId !== undefined) {
      return repo.find<D>(existingId);
    }
    const handle = repo.create<D>(initialDoc);
    map.set(key, handle.documentId);
    return handle;
  };
}

// ─── $meshState ─────────────────────────────────────────────────────────────

/**
 * Create a peer-replicated state primitive backed by Automerge with a mesh
 * transport. Every device holds a full replica; no central server holds a
 * replica. Operations flow peer-to-peer through signed and encrypted
 * messages on the underlying transport.
 *
 * @example
 * ```ts
 * const journal = $meshState<Journal>("journal", { entries: [] });
 * await journal.loaded;
 * journal.value = { entries: ["my private thoughts"] };
 * ```
 */
export function $meshState<T extends VersionedDoc>(
  key: string,
  initialValue: T,
  options: MeshStateOptions = {}
): CrdtPrimitive<T> {
  const repo = resolveRepo(options.repo);
  return $crdtState<T>({
    key,
    primitive: "meshState",
    initialValue,
    getHandle: buildHandleFactory<T>(repo, key, initialValue),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $meshText ──────────────────────────────────────────────────────────────

/**
 * Create a peer-replicated text primitive backed by a mesh transport.
 * Concurrent character-level edits from peers merge cleanly via Automerge's
 * updateText splicing, and every operation is signed and encrypted before
 * leaving the originating peer.
 */
export function $meshText(
  key: string,
  initialValue: string,
  options: MeshStateOptions = {}
): SpecialisedPrimitive<string> {
  const repo = resolveRepo(options.repo);
  return $crdtText(key, initialValue, {
    primitive: "meshState",
    getHandle: buildHandleFactory<TextDoc>(repo, key, { text: initialValue }),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $meshCounter ───────────────────────────────────────────────────────────

/**
 * Create a peer-replicated counter primitive backed by a mesh transport.
 * Concurrent increments commute, and every operation is signed and
 * encrypted before leaving the originating peer.
 */
export function $meshCounter(
  key: string,
  initialValue: number,
  options: MeshStateOptions = {}
): SpecialisedPrimitive<number> {
  const repo = resolveRepo(options.repo);
  return $crdtCounter(key, initialValue, {
    primitive: "meshState",
    getHandle: buildHandleFactory<CounterDoc>(repo, key, {}),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $meshList ──────────────────────────────────────────────────────────────

/**
 * Create a peer-replicated list primitive backed by a mesh transport.
 * Phase 0 naive replacement applies to writes for now; Phase 1.1 will
 * refine with structural diff-to-splice for concurrent insert/remove
 * preservation.
 */
export function $meshList<T>(
  key: string,
  initialValue: T[],
  options: MeshStateOptions = {}
): SpecialisedPrimitive<T[]> {
  const repo = resolveRepo(options.repo);
  return $crdtList<T>(key, initialValue, {
    primitive: "meshState",
    getHandle: buildHandleFactory<ListDoc<T>>(repo, key, { items: initialValue }),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}
