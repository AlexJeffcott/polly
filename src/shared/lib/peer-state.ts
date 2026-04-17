/**
 * peer-state — Phase 1 wrappers exposing $peerState, $peerText, $peerCounter,
 * and $peerList. These are the application-facing constructors for the middle
 * resilience tier in RFC-041: every device is a full Automerge replica, the
 * server included, and server-side code can read and mutate document contents
 * because the server participates in the data plane as an ordinary peer.
 *
 * Each primitive wraps the corresponding Phase 0 base ($crdtState, $crdtText,
 * $crdtCounter, $crdtList) with three additions:
 *
 *   1. The `primitive` label is hard-coded to "peerState" so the
 *      primitive-registry collision detection knows which family the key
 *      belongs to.
 *
 *   2. A handle factory that resolves the application's logical key to an
 *      Automerge DocumentId via a per-Repo key map. The first time a key is
 *      registered, the factory creates a new document on the configured Repo
 *      and records the mapping. On subsequent constructions of the same key,
 *      the factory looks up the existing DocumentId and finds the handle.
 *
 *   3. The `sign` option field validates that the configured Repo was
 *      created with signing enabled (via createPeerStateClient with
 *      `sign: true`). Signing adds Byzantine defence at the transport
 *      level without preventing the server from reading document
 *      contents. Encryption is not offered on $peerState because it
 *      would prevent the server from participating as an Automerge
 *      peer; applications that want encrypted state should use $meshState.
 *
 * The Repo itself is supplied by the application via {@link configurePeerState}
 * or per-call via the `repo` option. There is no transport in this Phase 1
 * cut — applications use a local-only Repo and document operations stay
 * inside the calling process. Phase 1's WebSocket relay adapter will plug in
 * via the same configuration path; Phase 2's mesh adapter does the same for
 * $meshState.
 */

import type { DocHandle, DocumentId, Repo } from "@automerge/automerge-repo/slim";
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

/** Common option shape across all four $peer* primitives. */
export interface PeerStateOptions<T> {
  /** Override the default Repo for this primitive. Useful for tests and for
   * applications that maintain multiple Repos (rare). */
  repo?: Repo;
  /** Request per-op Ed25519 signing for this primitive. Signing is a
   * transport-level concern: pass `sign: true` to `createPeerStateClient`
   * to enable it for all primitives on that Repo. Passing `sign: true`
   * here validates that the configured Repo was created with signing
   * enabled and throws if it was not. */
  sign?: boolean;
  /** Schema version target for the application. Migrations run on load. */
  schemaVersion?: number;
  /** Migration table keyed by target version. Required if schemaVersion is set. */
  migrations?: Migrations;
  /** Declarative read/write access. Compiled into a server share policy
   * once the relay transport is wired in. */
  access?: Access;
  /** Initial value used when this primitive's key has not been registered
   * before. Phase 0 callers passed this positionally; Phase 1 application
   * code does the same. */
  initialValue?: T;
}

/** Internal: per-Repo key → DocumentId map. Cleared by configurePeerState. */
const keyMapsByRepo = new WeakMap<Repo, Map<string, DocumentId>>();
/** Internal: set of Repos configured with signing enabled. */
const signingEnabledRepos = new WeakSet<Repo>();
let defaultRepo: Repo | undefined;

/**
 * Set the default Repo that the $peer* primitives use when no `repo` option
 * is supplied. Calling this with a new Repo clears the per-Repo key map so
 * that tests start each scenario with a fresh document space.
 *
 * Production code typically calls this once at application startup with a
 * Repo configured for the relay transport. Tests call it before each scenario
 * with an in-memory Repo.
 */
export function configurePeerState(repo: Repo, options?: { signEnabled?: boolean }): void {
  defaultRepo = repo;
  keyMapsByRepo.set(repo, new Map());
  if (options?.signEnabled) {
    signingEnabledRepos.add(repo);
  }
}

/**
 * Reset the peer-state subsystem to its initial unconfigured state. Intended
 * for tests; production code should not call this.
 */
export function resetPeerState(): void {
  defaultRepo = undefined;
}

function resolveRepo(option: Repo | undefined): Repo {
  const repo = option ?? defaultRepo;
  if (!repo) {
    throw new Error(
      "Polly $peerState: no Repo configured. Call configurePeerState(repo) at startup or pass { repo } in the primitive options."
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

function validateSignOption(options: PeerStateOptions<unknown>, repo: Repo): void {
  if (!options.sign) return;
  if (!signingEnabledRepos.has(repo)) {
    throw new Error(
      "Polly $peerState: { sign: true } was passed to the primitive but the configured Repo does not have signing enabled. " +
        "Pass { sign: true, keyring: ... } to createPeerStateClient to enable signing at the transport level, " +
        "then call configurePeerState(client.repo, { signEnabled: true })."
    );
  }
}

/**
 * Build a getHandle factory that resolves a logical key to a DocHandle on
 * the supplied Repo. The first call creates a new document seeded with the
 * given initial value and records the (key → DocumentId) mapping; subsequent
 * calls look up the existing DocumentId and find the handle.
 */
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

// ─── $peerState ─────────────────────────────────────────────────────────────

/**
 * Create a peer-replicated state primitive backed by Automerge. Every device
 * holds a full replica; the server, when one is configured via the relay
 * transport, holds one too and participates in the sync protocol as an
 * ordinary peer. Server-side code can read and mutate document contents.
 *
 * @example
 * ```ts
 * const settings = $peerState<Settings>("settings", { theme: "dark" });
 * await settings.loaded;
 * settings.value = { theme: "light" };
 * ```
 */
export function $peerState<T extends VersionedDoc>(
  key: string,
  initialValue: T,
  options: PeerStateOptions<T> = {}
): CrdtPrimitive<T> {
  const repo = resolveRepo(options.repo);
  validateSignOption(options, repo);
  return $crdtState<T>({
    key,
    primitive: "peerState",
    initialValue,
    getHandle: buildHandleFactory<T>(repo, key, initialValue),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $peerText ──────────────────────────────────────────────────────────────

export interface PeerTextOptions extends Omit<PeerStateOptions<unknown>, "initialValue"> {}

/**
 * Create a peer-replicated text primitive. Concurrent character-level edits
 * from peers merge cleanly via Automerge's updateText splicing.
 */
export function $peerText(
  key: string,
  initialValue: string,
  options: PeerTextOptions = {}
): SpecialisedPrimitive<string> {
  const repo = resolveRepo(options.repo);
  validateSignOption(options, repo);
  return $crdtText(key, initialValue, {
    primitive: "peerState",
    getHandle: buildHandleFactory<TextDoc>(repo, key, { text: initialValue }),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $peerCounter ───────────────────────────────────────────────────────────

export interface PeerCounterOptions extends Omit<PeerStateOptions<unknown>, "initialValue"> {}

/**
 * Create a peer-replicated counter primitive. Concurrent increments from
 * peers commute, so two clients each adding 1 to a counter at 5 produce a
 * counter at 7 after merging.
 */
export function $peerCounter(
  key: string,
  initialValue: number,
  options: PeerCounterOptions = {}
): SpecialisedPrimitive<number> {
  const repo = resolveRepo(options.repo);
  validateSignOption(options, repo);
  return $crdtCounter(key, initialValue, {
    primitive: "peerState",
    getHandle: buildHandleFactory<CounterDoc>(repo, key, {}),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}

// ─── $peerList ──────────────────────────────────────────────────────────────

export interface PeerListOptions extends Omit<PeerStateOptions<unknown>, "initialValue"> {}

/**
 * Create a peer-replicated list primitive. The Phase 0 base uses naive
 * whole-array replacement; Phase 1.1 will refine the write path with
 * structural diff-to-splice for concurrent insert/remove preservation.
 */
export function $peerList<T>(
  key: string,
  initialValue: T[],
  options: PeerListOptions = {}
): SpecialisedPrimitive<T[]> {
  const repo = resolveRepo(options.repo);
  validateSignOption(options, repo);
  return $crdtList<T>(key, initialValue, {
    primitive: "peerState",
    getHandle: buildHandleFactory<ListDoc<T>>(repo, key, { items: initialValue }),
    schemaVersion: options.schemaVersion,
    migrations: options.migrations,
    access: options.access,
  });
}
