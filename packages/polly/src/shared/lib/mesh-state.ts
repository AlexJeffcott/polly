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
 *      Automerge DocumentId by hashing the key into a deterministic,
 *      content-addressable id. Every Repo backed by the same storage lands
 *      on the same document without needing any extra state, and two devices
 *      that have never met converge on the same id for the same key — which
 *      also helps first-sync after pairing. (Prior to this change the factory
 *      held an in-memory per-Repo `Map<string, DocumentId>`, which meant that
 *      a lone-device reload — a very common onboarding state — produced a
 *      fresh DocumentId for the same logical key, orphaned the document the
 *      storage adapter still held on disk, and silently lost the user's data.)
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

import {
  Automerge,
  type BinaryDocumentId,
  type DocHandle,
  type DocumentId,
  interpretAsDocumentId,
  type Repo,
} from "@automerge/automerge-repo/slim";
import nacl from "tweetnacl";
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

let defaultRepo: Repo | undefined;

/** Per-module-instance identifier stamped at import time. Two distinct
 * module instances (e.g. duplicated under a bundler that hoists
 * differently for the consumer's app code and `@fairfox/polly`'s own
 * imports) produce two different ids — and therefore two different
 * `defaultRepo` globals.
 *
 * The polly#107 fingerprint reading is exactly that: `configureMeshState`
 * runs on one module instance (the one `createMeshClient` imports);
 * the consumer's `$meshState(key, initial)` calls run on a different
 * instance, whose `defaultRepo` was never set. `resolveRepo` either
 * throws (caught silently by consumer wrappers) or returns the
 * unconfigured fallback — either way, the handle that should land
 * in the mesh `Repo` lands somewhere else (or nowhere), Automerge's
 * NetworkSubsystem never sees it, and inbound sync from the daemon
 * has nowhere to go.
 *
 * Exported so consumers can compare the id seen at the `$meshState`
 * call site against the id seen at the `configureMeshState` call
 * site. A mismatch IS the bundle-duplication bug; a match rules it
 * out. The id is also surfaced via {@link getMeshStateModuleId} on
 * every `MeshClient.getPeerStateSnapshot()` so a single one-line
 * read from the failing tab tells the operator which module
 * instance the snapshot is rendered from.
 *
 * Polly issue #107 H5 (mesh-state module duplication). */
export const MESH_STATE_MODULE_ID: string = `mesh-state-${
  typeof crypto !== "undefined" && typeof crypto.randomUUID === "function"
    ? crypto.randomUUID()
    : Math.random().toString(36).slice(2) + Date.now().toString(36)
}`;

/** Returns the per-module-instance id stamped at import time. See
 * {@link MESH_STATE_MODULE_ID}. */
export function getMeshStateModuleId(): string {
  return MESH_STATE_MODULE_ID;
}

/** Last id passed to {@link configureMeshState}; the Repo's
 * `peerId` is captured at configuration time so a snapshot read can
 * answer "was this module instance ever wired to a mesh client at
 * all?". `undefined` means `$meshState` is reachable but no
 * `createMeshClient` call against THIS module instance ever
 * succeeded — the polly#107 H5 fingerprint. */
let lastConfiguredRepoPeerId: string | undefined;

/** Returns the `peerId` of the most recent Repo wired through
 * {@link configureMeshState} against this module instance. Surfaced
 * via the mesh client snapshot so a consumer can answer "did
 * configureMeshState run on the same module instance the wrappers
 * are using" in one read. */
export function getLastConfiguredRepoPeerId(): string | undefined {
  return lastConfiguredRepoPeerId;
}

/**
 * Set the default Repo that the $mesh* primitives use when no `repo` option
 * is supplied. Production code typically calls this once at application
 * startup with a Repo configured for the mesh transport. Tests call it
 * before each scenario with an in-memory or loopback Repo.
 */
export function configureMeshState(repo: Repo): void {
  defaultRepo = repo;
  lastConfiguredRepoPeerId = repo.peerId as unknown as string | undefined;
}

/**
 * Reset the mesh-state subsystem to its initial unconfigured state.
 * Intended for tests; production code should not call this.
 */
export function resetMeshState(): void {
  defaultRepo = undefined;
  lastConfiguredRepoPeerId = undefined;
  meshStateEverResolved = false;
  lazyInvocations = 0;
  lazyReachedRepo = 0;
  lastLoadedRejection = undefined;
  lastStorageOpenError = undefined;
  lazyWrappers = [];
  docIdResolver = undefined;
}

/** Returns whether this module instance's `defaultRepo` was ever
 * set via {@link configureMeshState}. Distinct from "was set and
 * then reset" — `resetMeshState` clears it. The polly#107 H5
 * fingerprint is `false` here on the module instance the consumer's
 * `$meshState` calls resolve from. */
export function isMeshStateConfigured(): boolean {
  return defaultRepo !== undefined;
}

/** Set to `true` once any `$meshState`-family wrapper has been
 * called against this module instance. Surfaced via
 * {@link wasMeshStateResolved} so a snapshot can answer "did any
 * wrapper code ever reach THIS module" — the polly#107 H5
 * fingerprint pair (`configured: false` AND `wasResolved: true`)
 * confirms the consumer's wrappers reach a different module instance
 * than `createMeshClient` configured. */
let meshStateEverResolved = false;

/** Returns `true` once any `$meshState`-family wrapper has been
 * called against this module instance. See
 * {@link meshStateEverResolved}. */
export function wasMeshStateResolved(): boolean {
  return meshStateEverResolved;
}

/** Polly#107 post-H5 instrumentation. Counts every invocation of
 * the lazy handle factory built by {@link buildHandleFactory} — i.e.
 * every time a `$meshState`-family primitive's underlying loader is
 * actually called. Compared against {@link lazyReachedRepo}, the gap
 * pinpoints whether throws are happening between factory entry and
 * the first `repo.*` touch.
 *
 * The polly#107 v0.58.0 fingerprint from `fairfox.fly.dev` ruled out
 * H5: the wrappers ARE reaching the same module instance the mesh
 * client configured. But `repo.handles` still reported one handle of
 * the expected fourteen, so something is throwing between the
 * wrapper's factory entry and the registration. These two counters
 * answer "where" without another diagnostic build. */
let lazyInvocations = 0;

/** Returns the count of factory invocations since module load. See
 * {@link lazyInvocations}. */
export function getLazyInvocations(): number {
  return lazyInvocations;
}

/** Polly#107 post-H5 instrumentation. Counts every time a factory
 * invocation made it as far as a `repo.find` / `repo.import` /
 * `repo.handles[...]` / `repo.storageSubsystem` call — i.e. the
 * factory reached the Repo subsystem before throwing or returning.
 * If {@link lazyInvocations} ticks but this counter does not, the
 * throw is happening before any Repo work; if both tick, the throw
 * (or the failing async path) is downstream of the Repo touch and
 * the next diagnostic should target Automerge's load/sync path. */
let lazyReachedRepo = 0;

/** Returns the count of factory invocations that reached
 * `repo.find` / `repo.import` since module load. See
 * {@link lazyReachedRepo}. */
export function getLazyReachedRepo(): number {
  return lazyReachedRepo;
}

/** Polly#107 post-H5 instrumentation. Records the most recent
 * rejection (or synchronous throw) escaping the factory body — the
 * `loaded` promise's rejection path. Today an unawaited rejection
 * inside a consumer wrapper vanishes without trace; capturing the
 * message + stack here on the module and exposing it via the
 * snapshot leaves a breadcrumb the operator can read in one paste.
 *
 * The format is the JSON-safe `{ name, message, stack, at }` shape
 * so the snapshot read does not have to traffic in `Error`
 * instances. `at` is `Date.now()` at the time the rejection was
 * captured. */
export interface MeshStateLoadedRejectionBreadcrumb {
  name: string;
  message: string;
  stack: string | undefined;
  at: number;
}
let lastLoadedRejection: MeshStateLoadedRejectionBreadcrumb | undefined;

/** Returns the most recent rejection escaping a `$meshState` factory
 * invocation since module load. See {@link lastLoadedRejection}. */
export function getLastLoadedRejection(): MeshStateLoadedRejectionBreadcrumb | undefined {
  return lastLoadedRejection;
}

function recordLoadedRejection(thrown: unknown): void {
  const err =
    thrown instanceof Error
      ? thrown
      : new Error(typeof thrown === "string" ? thrown : String(thrown));
  lastLoadedRejection = {
    name: err.name,
    message: err.message,
    stack: err.stack,
    at: Date.now(),
  };
}

/** Polly#107 post-v0.60 instrumentation. Default timeout for the two
 * storage-touching `await`s inside {@link buildHandleFactory} — the
 * `cached.whenReady(["ready", "unavailable"])` wait on a placeholder
 * handle, and the `repo.storageSubsystem.loadDoc()` read against
 * whatever IndexedDB adapter the consumer wired. Healthy completions
 * for both are normally sub-millisecond; the v0.60.0 fingerprint
 * showed 17 factories hung indefinitely against a wedged
 * `fairfox-mesh` IndexedDB that only released when Chrome itself
 * restarted. Five seconds is two orders of magnitude beyond the
 * normal upper bound and well below the operator's "have I been
 * staring at a stuck app" threshold — long enough that healthy
 * boots never trip the timeout and short enough that the next
 * polly#107-shaped session sees a populated {@link storageOpenError}
 * within the first few seconds of inspection. */
const STORAGE_OP_TIMEOUT_MS = 5000;

/** Polly#107 post-v0.60 instrumentation. Captured when a storage
 * read from inside a `$meshState`-family factory exceeds
 * {@link STORAGE_OP_TIMEOUT_MS}. Names which op timed out
 * (`whenReady`, `loadDoc`), the document id under attempt, the
 * elapsed time, and a single human-readable message that the
 * snapshot can paste verbatim into a ticket. The breadcrumb also
 * flows into {@link lastLoadedRejection} so the existing
 * "did anything reject" channel surfaces it alongside.
 *
 * The v0.60.0 fingerprint diagnosed "factories hung mid-await,
 * not throwing" indirectly — empty {@link lazyWrappers} beside
 * non-zero {@link lazyInvocations} / {@link lazyReachedRepo}. With
 * this field a future polly#107-shaped session reads
 * `storageOpenError.message: "Polly $meshState: storage operation
 * 'loadDoc' on document '<id>' timed out after 5000ms"` and jumps
 * directly to "the storage layer is hung; clear site data,"
 * skipping every other rung in the ladder. */
export interface MeshStateStorageOpenError {
  /** Which await in `buildHandleFactory` exceeded the timeout. */
  operation: "whenReady" | "loadDoc";
  /** Stringified Automerge `DocumentId` that was under attempt. */
  documentId: string;
  /** Time the operation was given before the timeout fired (ms). */
  timeoutMs: number;
  /** Wall-clock elapsed when the timeout fired (ms). Always
   * `>= timeoutMs`; a small overshoot is normal. */
  elapsedMs: number;
  /** Pre-formatted human-readable message. Identical to what
   * flows into {@link lastLoadedRejection}.message. */
  message: string;
  /** `Date.now()` at the moment the timeout fired. */
  at: number;
}

let lastStorageOpenError: MeshStateStorageOpenError | undefined;

/** Returns the most recent storage-operation timeout escaping a
 * `$meshState` factory invocation since module load. See
 * {@link lastStorageOpenError}. */
export function getStorageOpenError(): MeshStateStorageOpenError | undefined {
  return lastStorageOpenError;
}

function recordStorageOpenError(error: MeshStateStorageOpenError): void {
  lastStorageOpenError = error;
}

/** Polly#107 post-v0.60 instrumentation. Wraps the storage-touching
 * awaits inside {@link buildHandleFactory} with a hard timeout. On
 * timeout the rejection feeds both {@link lastLoadedRejection} (so
 * the existing channel surfaces it) and {@link lastStorageOpenError}
 * (so a snapshot read distinguishes "storage layer wedged" from
 * any other factory rejection in one field). */
async function withStorageTimeout<T>(
  operation: "whenReady" | "loadDoc",
  documentId: string,
  promise: Promise<T>,
  timeoutMs: number = STORAGE_OP_TIMEOUT_MS
): Promise<T> {
  const start = Date.now();
  let timer: ReturnType<typeof setTimeout> | undefined;
  let timedOut = false;
  try {
    return await new Promise<T>((resolve, reject) => {
      timer = setTimeout(() => {
        timedOut = true;
        const elapsedMs = Date.now() - start;
        const message = `Polly $meshState: storage operation '${operation}' on document '${documentId}' timed out after ${timeoutMs}ms`;
        recordStorageOpenError({
          operation,
          documentId,
          timeoutMs,
          elapsedMs,
          message,
          at: Date.now(),
        });
        reject(new Error(message));
      }, timeoutMs);
      promise.then(
        (value) => {
          if (!timedOut) resolve(value);
        },
        (err) => {
          if (!timedOut) reject(err);
        }
      );
    });
  } finally {
    if (timer !== undefined) clearTimeout(timer);
  }
}

/** Polly#107 post-v0.59 instrumentation. Categorises the exit path
 * a `$mesh*` lazy factory invocation took. The v0.59.0 fingerprint
 * showed `lazyInvocations === lazyReachedRepo === 17` and no
 * `lastLoadedRejection` — every factory reached the first
 * `repo.handles[docId]` access, none rejected loudly, yet 16 of 17
 * handles never landed in `repo.handles`. Without per-exit detail
 * the snapshot cannot disambiguate "factory returned the cached
 * handle", "factory hydrated from storage", "factory seeded and
 * imported a fresh doc", or "factory took the cached branch but
 * `whenReady` resolved to `unavailable` and the code fell
 * through". Each exit reason corresponds to a single line in
 * {@link buildHandleFactory}; the snapshot record names it
 * verbatim so the operator can grep the source from one read. */
export type LazyWrapperExitReason =
  | "returned-cached"
  | "loaded-from-storage"
  | "seeded-and-imported"
  | "threw";

/** Polly#107 post-v0.59 instrumentation. One record per factory
 * invocation, ring-buffered on the module and surfaced through
 * `MeshClient.getPeerStateSnapshot()` as
 * `meshStateModule.lazyWrappers`. The five fields together answer
 * the post-v0.59 question "if every factory reached the Repo and
 * nothing rejected, why are 16 of 17 handles absent from
 * `repo.handles`?" — `exitReason` names which of the three success
 * paths each took, `handleRegistered` is the synchronous peek at
 * `repo.handles[docId]` taken in the factory's `finally` (i.e. at
 * the moment of would-be return), and `handleState` is the
 * lifecycle state observed in that peek. A row where
 * `exitReason: "seeded-and-imported"` and `handleRegistered: false`
 * is the smoking gun for H-Q1 (`repo.import` returned without
 * registering); rows where `exitReason: "returned-cached"` repeats
 * for sixteen of seventeen distinct keys indicates collisions or
 * that the factory is being called multiple times against a
 * Repo-state-machine that has already filled the slot. */
export interface MeshStateLazyWrapperRecord {
  /** The logical application key passed to `$meshState(key, ...)`. */
  key: string;
  /** Stringified Automerge `DocumentId` derived from the key. */
  docId: string;
  /** `Date.now()` captured at the moment the factory was about to
   * return (or rethrow). */
  at: number;
  /** Which of the four exit paths the factory took. See
   * {@link LazyWrapperExitReason}. */
  exitReason: LazyWrapperExitReason;
  /** Snapshot peek `repo.handles[docId] !== undefined` taken in the
   * factory's `finally` clause. `true` means the local Repo
   * registered the handle; `false` means the factory thinks it
   * succeeded but the Repo does not hold the handle for this
   * documentId. The "polly#107 post-v0.59" smoking gun is
   * `exitReason: "seeded-and-imported", handleRegistered: false`. */
  handleRegistered: boolean;
  /** Lifecycle state of `repo.handles[docId]` at the synchronous
   * peek time. `undefined` when the handle was not registered.
   * Useful for distinguishing the "registered as loading/unavailable"
   * case from the "registered as ready" case. */
  handleState: string | undefined;
  /** Error message if `exitReason === "threw"`; `undefined`
   * otherwise. The full rejection still flows into
   * {@link lastLoadedRejection}; this field is the row-local
   * summary so the snapshot can show the failure cause inline. */
  errorMessage: string | undefined;
}

/** Bounded ring of {@link MeshStateLazyWrapperRecord} captured per
 * factory invocation. Cap kept low so the snapshot stays small
 * enough to paste into a ticket; fairfox's realistic pre-warm count
 * is in the high teens, so 64 leaves plenty of headroom and still
 * truncates pathological logs.
 *
 * Reading guide for a future polly#107-shaped session:
 *
 * - `lazyWrappers: 0 records, lazyInvocations > 0` means the
 *   factories are **hung mid-await, not throwing** — the buffer
 *   itself is fine; the records simply never reached the `finally`
 *   that writes them. The v0.60.0 fingerprint took this exact shape
 *   and turned out to be a wedged `fairfox-mesh` IndexedDB the
 *   process could no longer evict; restarting Chrome cleared it.
 *   `storageOpenError` (added v0.61.0) now populates within
 *   {@link STORAGE_OP_TIMEOUT_MS}ms of the hang and names the
 *   operation, so this state is rarely empty in practice — but if
 *   `lazyInvocations > 0`, `storageOpenError` is unset, and the
 *   buffer is empty, the factories are hung somewhere other than
 *   the two timeout-wrapped awaits and the next diagnostic should
 *   trace each entry in {@link buildHandleFactory} individually.
 * - `lazyWrappers: N records, repoHandleCount < N` is the original
 *   v0.59.0 question; the per-record `exitReason` and
 *   `handleRegistered` fields answer it directly. */
const LAZY_WRAPPER_LOG_CAP = 64;
let lazyWrappers: MeshStateLazyWrapperRecord[] = [];

/** Returns a copy of the lazy-wrapper invocation log. See
 * {@link MeshStateLazyWrapperRecord}. */
export function getLazyWrappers(): MeshStateLazyWrapperRecord[] {
  return lazyWrappers.slice();
}

function recordLazyWrapper(record: MeshStateLazyWrapperRecord): void {
  lazyWrappers.push(record);
  if (lazyWrappers.length > LAZY_WRAPPER_LOG_CAP) {
    lazyWrappers = lazyWrappers.slice(-LAZY_WRAPPER_LOG_CAP);
  }
}

function peekHandleState(repo: Repo, documentId: DocumentId): string | undefined {
  const handle = (repo.handles as unknown as Record<string, { state: unknown } | undefined>)[
    documentId as unknown as string
  ];
  if (!handle) return undefined;
  return typeof handle.state === "string" ? handle.state : String(handle.state ?? "unknown");
}

function resolveRepo(option: Repo | undefined): Repo {
  meshStateEverResolved = true;
  const repo = option ?? defaultRepo;
  if (!repo) {
    // Leave a breadcrumb on the console for the polly#107 H5
    // fingerprint even if the consumer's wrappers catch the throw.
    // The id pinpoints WHICH module instance landed here so the
    // operator can compare against the one `createMeshClient`
    // configured.
    if (typeof console !== "undefined" && typeof console.warn === "function") {
      console.warn(
        `[polly#107 H5] $meshState resolved against unconfigured module instance ${MESH_STATE_MODULE_ID}. If createMeshClient was called elsewhere, the consumer's wrappers and the mesh client are reaching different module instances — see polly#107.`
      );
    }
    throw new Error(
      `Polly $meshState: no Repo configured (module instance ${MESH_STATE_MODULE_ID}). Call configureMeshState(repo) at startup or pass { repo } in the primitive options. If you have called configureMeshState elsewhere, the most likely cause is that the call resolved to a different module instance than this one — see polly#107.`
    );
  }
  return repo;
}

/**
 * Domain-separated hash of an application key into a 16-byte
 * {@link BinaryDocumentId}. SHA-512 via tweetnacl (already a dep for signing);
 * the first 16 bytes give a DocumentId with uniform distribution across the
 * Automerge id space. The domain prefix pins the derivation to $meshState so
 * that the same logical key used in a different Polly subsystem would
 * produce a different id.
 */
const DOC_ID_DOMAIN = "polly/meshState/v1";
const keyEncoder = new TextEncoder();

/**
 * Domain-separated hash of an application key into a 16-byte
 * {@link DocumentId}. Exported so consumers can compute the
 * derived id for any logical key — useful for ADR 0008-style
 * document compaction where the consumer wants to seed a new doc
 * at `deriveDocumentId(key + ':v' + timestamp)` and stash that id
 * in a runtime index. */
export function deriveDocumentId(key: string): DocumentId {
  const digest = nacl.hash(keyEncoder.encode(`${DOC_ID_DOMAIN}:${key}`));
  const bytes = digest.slice(0, 16);
  return interpretAsDocumentId(bytes as unknown as BinaryDocumentId);
}

/**
 * Caller-installed resolver consulted at every `$mesh*` wrapper
 * lazy construction. Returns the {@link DocumentId} the consumer
 * wants the logical key to resolve to, or `undefined` to fall back
 * to the deterministic {@link deriveDocumentId} path.
 *
 * Designed for fairfox-style document compaction where a logical
 * key (e.g. `mesh:devices`) needs to point at a freshly-seeded
 * cleaned doc instead of the bloated historical one. The consumer
 * registers a resolver that consults a runtime index document
 * (e.g. `mesh:document-index`) for the current docId per key,
 * falling back to derived for keys that haven't been compacted.
 *
 * Synchronous: the resolver runs inside `$meshState` construction,
 * which is called from consumer module-init paths that can't
 * tolerate an async hop. Consumers that need an async lookup
 * (e.g. waiting for an index doc to hydrate) typically register
 * the resolver only after the index has loaded, and the
 * pre-registration period uses the legacy derived path.
 *
 * Note on recursion: a consumer's index doc is itself a `$meshState`
 * wrapper that goes through this resolver. The resolver must
 * short-circuit on its own index-doc key (return `undefined`) or
 * the resolution will recurse infinitely. Per ADR 0008.
 */
export type DocIdResolver = (key: string) => DocumentId | undefined;

let docIdResolver: DocIdResolver | undefined;

export function registerDocIdResolver(resolver: DocIdResolver | undefined): void {
  docIdResolver = resolver;
}

export function getDocIdResolver(): DocIdResolver | undefined {
  return docIdResolver;
}

/**
 * Resolve a logical `$meshState` key to a {@link DocumentId}. The
 * caller-installed {@link DocIdResolver} (if any) wins; falls back
 * to {@link deriveDocumentId}. ADR 0008.
 */
export function resolveDocumentId(key: string): DocumentId {
  return docIdResolver?.(key) ?? deriveDocumentId(key);
}

/**
 * Caller-installed detector consulted after a `$mesh*` wrapper's
 * handle reaches `ready`. Inspects the loaded doc; returns a
 * {@link DocumentId} the wrapper should transparently rebind to,
 * or `undefined` to keep the current handle.
 *
 * Designed for fairfox-style document-compaction redirects: when a
 * doc carries an in-band sentinel field (e.g. `__compaction__`),
 * the wrapper's first load gets the sealed doc; the detector reads
 * the sentinel and returns the migrated-to docId; polly swaps to
 * that handle and the consumer sees the cleaned doc transparently.
 *
 * Symmetric with {@link DocIdResolver}: the resolver runs at lazy
 * construction (synchronous, no doc available); the detector runs
 * after first load (synchronous over the materialised doc). Either
 * is sufficient to redirect a wrapper, but the detector is the only
 * mechanism that works on a device whose redirect-index hasn't yet
 * synced — the sealed doc carries enough information on its own to
 * resolve the redirect from local storage.
 *
 * The detector is invoked repeatedly along a chain of redirects
 * with a hard cycle/depth guard (see {@link MAX_REDIRECT_FOLLOWS}),
 * so a compacted-then-compacted-again doc resolves to the latest
 * `currentDocId` in one factory call.
 */
export type RedirectDetector = (doc: unknown) => DocumentId | undefined;

let redirectDetector: RedirectDetector | undefined;

export function registerRedirectDetector(detector: RedirectDetector | undefined): void {
  redirectDetector = detector;
}

export function getRedirectDetector(): RedirectDetector | undefined {
  return redirectDetector;
}

/** Hard cap on the redirect-follow loop. A correctly-behaved
 * detector terminates in one or two hops (sealed → current; rarely
 * sealed1 → sealed2 → current after a re-compaction). Anything
 * past this is either a cycle (bug in the detector) or an attacker
 * trying to wedge the wrapper. */
const MAX_REDIRECT_FOLLOWS = 8;

/**
 * Build a getHandle factory that resolves a logical key to a DocHandle on
 * the supplied Repo via a deterministic DocumentId. On the first call during
 * a process lifetime — whether the device has never written this key or has
 * written it before a prior reload — the factory short-circuits around
 * {@link Repo.find}'s network-request timeout: it peeks directly at the
 * Repo's storage subsystem, hydrates from storage if the bytes are there,
 * and otherwise seeds a fresh document at the deterministic id. Subsequent
 * calls in the same process return the cached handle.
 */
function buildHandleFactory<D>(
  repo: Repo,
  key: string,
  initialDoc: D
): () => Promise<DocHandle<D>> {
  // ADR 0008: consult the caller-installed resolver first so a
  // compacted key can point at the freshly-seeded cleaned doc.
  // Falls back to the deterministic derived id when no resolver is
  // registered or the resolver returns undefined.
  const documentId = resolveDocumentId(key);
  return async () => {
    // Polly#107 post-H5: tick on every factory entry. See
    // {@link lazyInvocations} for the diagnostic this enables.
    lazyInvocations++;
    let exitReason: LazyWrapperExitReason = "threw";
    let errorMessage: string | undefined;
    try {
      const cached = repo.handles[documentId];
      // Touching `repo.handles` is the first Repo subsystem read; if
      // the throw happens after this line we know the factory got
      // past the Repo-identity gate.
      lazyReachedRepo++;
      const docIdString = documentId as unknown as string;
      let handle: DocHandle<D>;
      if (cached) {
        // Polly#107 post-v0.60: bound the placeholder-handle wait so
        // a wedged storage layer (e.g. zombie IDB connection holding
        // a `loading` handle hostage) surfaces as a timed-out
        // `storageOpenError` within seconds instead of hanging the
        // factory indefinitely.
        await withStorageTimeout(
          "whenReady",
          docIdString,
          cached.whenReady(["ready", "unavailable"])
        );
        if (cached.state === "ready") {
          exitReason = "returned-cached";
          handle = cached as unknown as DocHandle<D>;
        } else {
          // Fall through to the load/seed path below.
          handle = await loadOrSeed<D>(repo, documentId, initialDoc, docIdString, (r) => {
            exitReason = r;
          });
        }
      } else {
        handle = await loadOrSeed<D>(repo, documentId, initialDoc, docIdString, (r) => {
          exitReason = r;
        });
      }
      // ADR 0008 v3b: the redirect detector runs INSIDE
      // {@link $crdtState} on every doc change, not here. The
      // factory's job is to produce the initial handle for the
      // resolver-derived docId; $crdtState handles continuous
      // sentinel-follow against the live handle so a peer-synced
      // sentinel rebinds the wrapper reactively without a reload.
      return handle;
    } catch (err) {
      // Capture the breadcrumb on the module so an otherwise-silent
      // unawaited rejection in a consumer wrapper leaves a trace the
      // snapshot can surface. See {@link lastLoadedRejection}.
      errorMessage = err instanceof Error ? err.message : String(err);
      recordLoadedRejection(err);
      throw err;
    } finally {
      // Polly#107 post-v0.59: peek `repo.handles[documentId]` at the
      // moment of would-be return so the snapshot can name, per
      // factory invocation, which exit path was taken AND whether
      // the Repo's local-side bookkeeping actually committed the
      // handle. The catch arm has already set `exitReason = "threw"`
      // by default; the success arms overwrite it before returning,
      // so the `finally`'s reading is correct in all four cases.
      const handleState = peekHandleState(repo, documentId);
      recordLazyWrapper({
        key,
        docId: documentId as unknown as string,
        at: Date.now(),
        exitReason,
        handleRegistered: handleState !== undefined,
        handleState,
        errorMessage,
      });
    }
  };
}

/** Domain-separated derivation of an Automerge actor id from a {@link DocumentId}.
 * Two peers that take the {@link loadOrSeed} path concurrently against the
 * same docId would otherwise each call `Automerge.from(initialDoc)` with a
 * fresh random actor, producing two independent top-level field assignments
 * that Automerge resolves by last-writer-wins-per-field on merge — orphaning
 * the losing seed's map and every per-key write that lived inside it (#113).
 *
 * Deriving the seed actor from the docId pins both peers to the same actor.
 * Combined with a fixed `time: 0` on the seed change (see {@link seedDocumentBytes}),
 * the seed change carries an identical hash on every peer. Automerge dedupes
 * by change hash, so the merge sees one change instead of two concurrent
 * ones and the top-level fields anchor to a single map. Subsequent per-key
 * writes use the peer's own random actor and merge cleanly.
 *
 * The domain prefix is separate from {@link DOC_ID_DOMAIN} so the seed-actor
 * derivation cannot collide with the docId derivation even if a future
 * change reuses one of the byte ranges. */
const SEED_ACTOR_DOMAIN = "polly/meshState/seedActor/v1";

/** Produce the 16-byte hex actor id Automerge uses as the seed's authorship
 * stamp. 16 bytes (32 hex chars) is the conventional Automerge actor-id
 * width; the WASM layer accepts any hex string but matching the convention
 * keeps debug output readable. */
function deriveSeedActor(documentId: DocumentId): string {
  const docIdString = documentId as unknown as string;
  const digest = nacl.hash(keyEncoder.encode(`${SEED_ACTOR_DOMAIN}:${docIdString}`));
  let hex = "";
  for (let i = 0; i < 16; i++) {
    hex += (digest[i] ?? 0).toString(16).padStart(2, "0");
  }
  return hex;
}

/** Build the seed bytes for {@link loadOrSeed}. Pre-#113 this was a single
 * `Automerge.save(Automerge.from(initialDoc))` call, which produced a fresh
 * random actor and a `Date.now()`-stamped change on every peer — two peers
 * seeding the same docId concurrently would then race at the top-level
 * field-assignment boundary on merge.
 *
 * The fix builds the seed deterministically: a docId-derived actor and a
 * fixed `time: 0` on the change make the seed bytes identical across every
 * peer that takes this path for the same docId, so Automerge dedupes the
 * seed change on merge.
 *
 * Set `POLLY_113_DISABLE_FIX=1` to restore the pre-fix non-deterministic
 * behaviour. Used by `tests/unit/mesh-state.test.ts` to prove the
 * failing-shape repro catches the regression. */
function seedDocumentBytes<D>(documentId: DocumentId, initialDoc: D): Uint8Array {
  const disable = typeof process !== "undefined" && process.env?.["POLLY_113_DISABLE_FIX"] === "1";
  if (disable) {
    return Automerge.save(Automerge.from(initialDoc as unknown as Record<string, unknown>));
  }
  const actor = deriveSeedActor(documentId);
  const empty = Automerge.init<Record<string, unknown>>({ actor });
  const seeded = Automerge.change(empty, { time: 0 }, (d: Record<string, unknown>) => {
    const source = initialDoc as unknown as Record<string, unknown>;
    for (const key of Object.keys(source)) {
      d[key] = source[key];
    }
  });
  return Automerge.save(seeded);
}

/** Helper for the load-or-seed arm of {@link buildHandleFactory}.
 * Extracted so the cached/non-cached arms share one body. */
async function loadOrSeed<D>(
  repo: Repo,
  documentId: DocumentId,
  initialDoc: D,
  docIdString: string,
  setExitReason: (r: LazyWrapperExitReason) => void
): Promise<DocHandle<D>> {
  const loadPromise = repo.storageSubsystem?.loadDoc<D>(documentId);
  const stored = loadPromise
    ? await withStorageTimeout("loadDoc", docIdString, loadPromise)
    : undefined;
  if (stored) {
    setExitReason("loaded-from-storage");
    return repo.find<D>(documentId, { allowableStates: ["ready"] });
  }
  const seeded = seedDocumentBytes(documentId, initialDoc);
  const handle = repo.import<D>(seeded, { docId: documentId });
  handle.doneLoading();
  setExitReason("seeded-and-imported");
  return handle;
}

/** Resolve a redirect off a ready handle, walking the detector
 * chain (up to {@link MAX_REDIRECT_FOLLOWS}) and returning the
 * final handle. Used by {@link $crdtState}'s continuous-rebind
 * loop. Symmetric structure to the docId resolver, but works
 * against the materialised doc once the handle is ready — so a
 * peer-synced sentinel on the bound doc transparently rebinds the
 * wrapper to the new docId without a reload. */
export async function followRedirects<D>(repo: Repo, initial: DocHandle<D>): Promise<DocHandle<D>> {
  let current = initial;
  const seen = new Set<string>([current.documentId as unknown as string]);
  for (let i = 0; i < MAX_REDIRECT_FOLLOWS; i++) {
    const detector = redirectDetector;
    if (!detector) {
      return current;
    }
    let nextId: DocumentId | undefined;
    try {
      const doc = current.doc();
      if (!doc) {
        return current;
      }
      nextId = detector(doc);
    } catch {
      // Detector threw — keep current handle.
      return current;
    }
    if (!nextId) {
      return current;
    }
    const nextIdString = nextId as unknown as string;
    if (nextIdString === (current.documentId as unknown as string)) {
      return current;
    }
    if (seen.has(nextIdString)) {
      // Cycle. Stop following; consumer sees the current handle.
      return current;
    }
    seen.add(nextIdString);
    try {
      // `allowableStates: ['ready', 'unavailable']` lets find resolve
      // when the new doc syncs from a peer OR when polly gives up
      // and marks it unavailable. The wrapper subscribes to the
      // handle either way, so a slow-syncing redirect target shows
      // up in the consumer's UI the moment the bytes arrive.
      current = await repo.find<D>(nextId, {
        allowableStates: ["ready", "unavailable"],
      });
    } catch {
      // Find threw — fall back to the previous handle.
      return current;
    }
  }
  return current;
}

// $meshState

/** Attach a rejection sink to a mesh primitive's `loaded` promise.
 * Polly#107 post-H5: an unawaited `loaded` rejection in a consumer
 * wrapper would vanish without trace; this captures the breadcrumb
 * on the module so a snapshot read can surface it. The original
 * primitive is returned unchanged — the `.catch` is a side-effect
 * sink that does not swallow the rejection from any consumer that
 * does await `loaded`. */
function attachLoadedRejectionSink<P extends { loaded: Promise<unknown> }>(primitive: P): P {
  primitive.loaded.catch((err) => {
    recordLoadedRejection(err);
  });
  return primitive;
}

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
  return attachLoadedRejectionSink(
    $crdtState<T>({
      key,
      primitive: "meshState",
      initialValue,
      getHandle: buildHandleFactory<T>(repo, key, initialValue),
      resolveRedirect: buildRedirectResolver<T>(repo),
      schemaVersion: options.schemaVersion,
      migrations: options.migrations,
      access: options.access,
    })
  );
}

/** Compose the caller-registered {@link RedirectDetector} (if any)
 * with the repo handle the wrapper is operating against, into the
 * `resolveRedirect` callback {@link $crdtState} consumes. Returns
 * `undefined` when no detector is registered, so $crdtState skips
 * the rebind path entirely and behaves exactly as it did pre-v3b.
 *
 * The closure captures the repo at construction time, so a later
 * {@link configureMeshState} call won't redirect an existing
 * wrapper to a different repo — matching how the initial handle is
 * resolved. */
function buildRedirectResolver<T>(
  repo: Repo
): ((handle: DocHandle<T>, doc: T) => Promise<DocHandle<T> | undefined>) | undefined {
  if (!redirectDetector) {
    // Detector might be registered later; return a callback that
    // checks at call time rather than locking in undefined now.
  }
  return async (_handle, doc) => {
    const detector = redirectDetector;
    if (!detector) return undefined;
    let nextId: DocumentId | undefined;
    try {
      nextId = detector(doc);
    } catch {
      return undefined;
    }
    if (!nextId) return undefined;
    try {
      return await repo.find<T>(nextId, {
        allowableStates: ["ready", "unavailable"],
      });
    } catch {
      return undefined;
    }
  };
}

// $meshText

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
  return attachLoadedRejectionSink(
    $crdtText(key, initialValue, {
      primitive: "meshState",
      getHandle: buildHandleFactory<TextDoc>(repo, key, { text: initialValue }),
      schemaVersion: options.schemaVersion,
      migrations: options.migrations,
      access: options.access,
    })
  );
}

// $meshCounter

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
  return attachLoadedRejectionSink(
    $crdtCounter(key, initialValue, {
      primitive: "meshState",
      getHandle: buildHandleFactory<CounterDoc>(repo, key, {}),
      schemaVersion: options.schemaVersion,
      migrations: options.migrations,
      access: options.access,
    })
  );
}

// $meshList

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
  return attachLoadedRejectionSink(
    $crdtList<T>(key, initialValue, {
      primitive: "meshState",
      getHandle: buildHandleFactory<ListDoc<T>>(repo, key, { items: initialValue }),
      schemaVersion: options.schemaVersion,
      migrations: options.migrations,
      access: options.access,
    })
  );
}
