/**
 * mesh-client — first-class factory for constructing a Polly mesh client.
 *
 * The mesh transport stack has five pieces that have to be wired together:
 * a {@link MeshSignalingClient} talking to the relay server, a
 * {@link MeshWebRTCAdapter} that owns the per-peer RTCPeerConnections, a
 * {@link MeshNetworkAdapter} that signs and encrypts every message on the
 * way through, an Automerge `Repo` that drives sync, and a `MeshKeyring`
 * that holds the crypto material. Prior to this module, every consuming
 * application had to assemble the five pieces by hand — and in Node or
 * Bun had to monkey-patch `globalThis.WebSocket` / `globalThis.RTCPeerConnection`
 * because the lower-level primitives reached for those globals.
 *
 * `createMeshClient` takes options, hands back a `MeshClient`, and also
 * calls `configureMeshState(client.repo)` so `$meshState` works without
 * a second setup step. The WebSocket and RTCPeerConnection implementations
 * are injectable; defaults read from `globalThis` for browser ergonomics.
 * The companion `@fairfox/polly/mesh/node` subpath provides a CLI bootstrap
 * helper that wires werift (or `@roamhq/wrtc` if the consumer prefers) and
 * a file-backed keyring store.
 */

import { type PeerId, Repo, type StorageAdapterInterface } from "@automerge/automerge-repo/slim";
import type { KeyringStorage } from "./keyring-storage";
import { emitMeshDiagnostic } from "./mesh-diagnostics";
import {
  DEFAULT_MESH_KEY_ID,
  MESH_CONTROL_TYPE,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "./mesh-network-adapter";
import { MeshSignalingClient, type MeshSignalingClientOptions } from "./mesh-signaling-client";
import {
  configureMeshState,
  getLastConfiguredRepoPeerId,
  getLastLoadedRejection,
  getLazyInvocations,
  getLazyReachedRepo,
  getLazyWrappers,
  getMeshStateModuleId,
  getStorageOpenError,
  isMeshStateConfigured,
  type MeshStateLazyWrapperRecord,
  type MeshStateLoadedRejectionBreadcrumb,
  type MeshStateStorageOpenError,
  wasMeshStateResolved,
} from "./mesh-state";
import { MeshWebRTCAdapter, type MeshWebRTCAdapterOptions } from "./mesh-webrtc-adapter";
import {
  applyRevocation,
  createRevocation,
  decodeRevocation,
  encodeRevocation,
  RevocationError,
  type RevocationRecord,
} from "./revocation";
import {
  decodeRevocationSummary,
  encodeRevocationSummary,
  type RevocationSummaryEntry,
} from "./revocation-summary";

/** Options for {@link createMeshClient}. */
export interface CreateMeshClientOptions {
  /** Signalling-server configuration. `peerId` must be the same identity
   * this client's keyring was paired with on other peers. */
  signaling: {
    url: string;
    peerId: string;
    /** Optional WebSocket ctor override (e.g. `ws` on old Node). Defaults
     * to `globalThis.WebSocket`. */
    WebSocket?: MeshSignalingClientOptions["WebSocket"];
    /** Forwarded error callback for diagnostic UI. */
    onError?: MeshSignalingClientOptions["onError"];
    /** Forwarded hook for custom signalling frames. See
     * {@link MeshSignalingClientOptions.onCustomFrame} — consumers who
     * layer application protocols on the signalling socket receive
     * frames of unknown types here. */
    onCustomFrame?: MeshSignalingClientOptions["onCustomFrame"];
  };
  /** WebRTC configuration. On browsers the defaults are fine; in Node or
   * Bun pass the `RTCPeerConnection` ctor from `werift` or `@roamhq/wrtc`. */
  rtc?: {
    RTCPeerConnection?: MeshWebRTCAdapterOptions["RTCPeerConnection"];
    iceServers?: RTCIceServer[];
    /**
     * Async resolver for ICE servers, called once at connect time. Wins
     * over `iceServers` if both are set. The realistic pattern is a
     * consumer fetching short-lived TURN credentials from its own
     * backend before each session — for production WebRTC apps that
     * care about coverage, TURN is the only way two peers behind
     * symmetric NATs (cellular CGNAT, some corporate firewalls) can
     * exchange bytes at all.
     *
     * Common provider shapes:
     *
     * - **Self-hosted coturn**: fetch a HMAC-derived ephemeral
     *   `username` / `credential` pair from your backend and return
     *   `[{ urls: "turn:turn.example.com", username, credential }]`.
     * - **Cloudflare Calls**: hit `/v1/turn/keys/<id>/credentials/generate`
     *   from a server route and pass the returned `iceServers` array
     *   straight through.
     * - **Twilio NTS**: call the network-traversal-service endpoint
     *   server-side and forward `data.iceServers`.
     * - **metered.ca / Xirsys / etc.**: same pattern — credentials live
     *   server-side, the resolver is the integration point.
     *
     * Resolution happens once. ICE restart with refreshed credentials
     * is a separate concern that this hook does not yet cover; if your
     * deployment needs it, tear down and rebuild the mesh client when
     * the credential window closes.
     */
    iceCredentialResolver?: () => Promise<RTCIceServer[]>;
    /** Forward of {@link MeshWebRTCAdapterOptions.iceTransportPolicy}.
     * Set to `"relay"` to force every candidate pair through TURN; the
     * default leaves the underlying {@link RTCPeerConnection}
     * implementation's default in place. The
     * `examples/mesh-large-initial-sync-turn` harness uses `"relay"` to
     * exercise the polly#105 real-transport contract. */
    iceTransportPolicy?: MeshWebRTCAdapterOptions["iceTransportPolicy"];
    /** Forward of {@link MeshWebRTCAdapterOptions.iceRelayEnforcement}.
     * Defaults to `true`. Set to `false` to bypass the polly#105
     * relay-only enforcement layer; the
     * `examples/mesh-large-initial-sync-turn` falsification path
     * (`POLLY_105_DISABLE_TURN_FIX=1`) does this to reproduce the
     * pre-#105 candidate-leak shape. Production callers should leave
     * this at the default. */
    iceRelayEnforcement?: MeshWebRTCAdapterOptions["iceRelayEnforcement"];
    dataChannelLabel?: string;
    /** How often the mesh client re-evaluates whether to dial peers
     * already present in the signalling roster against the live
     * keyring. The sweep is what makes
     * `applyPairingToken(token, keyring)` calls performed *after* the
     * mesh client is up take effect on the WebRTC layer without
     * requiring the consumer to call
     * {@link MeshClient.refreshKnownPeers} by hand — see polly issue
     * #103 for the failure mode this closes. Defaults to 2000ms; set
     * to 0 to disable (the captured-set-only behaviour, kept for
     * migrations and for the pre-fix demonstration shape in
     * `examples/mesh-recovery-pair`). Forwarded straight to
     * {@link MeshWebRTCAdapterOptions.knownPeersRefreshIntervalMs}. */
    knownPeersRefreshIntervalMs?: MeshWebRTCAdapterOptions["knownPeersRefreshIntervalMs"];
    /** Forward of {@link MeshWebRTCAdapterOptions.syncYieldEnabled}.
     * Defaults to `true`. The `examples/mesh-large-initial-sync`
     * example flips this to `false` when `POLLY_104_DISABLE_FIX=1` is
     * set, to demonstrate the pre-#104 tight-loop behaviour against
     * post-fix polly. Production callers should leave this at the
     * default. */
    syncYieldEnabled?: MeshWebRTCAdapterOptions["syncYieldEnabled"];
    /** Forward of
     * {@link MeshWebRTCAdapterOptions.syncFragmentChunkSizeOverride}.
     * Production callers should leave this undefined. The
     * `examples/mesh-large-initial-sync` example passes 64 KiB when
     * `POLLY_104_DISABLE_FIX=1` to recreate the pre-#104
     * fragmentation bug. */
    syncFragmentChunkSizeOverride?: MeshWebRTCAdapterOptions["syncFragmentChunkSizeOverride"];
  };
  /** The local peer's keyring — one of three shapes:
   *
   * - A {@link MeshKeyring} instance. The same object is used for the
   *   lifetime of the mesh client; in-place mutations to its `knownPeers`
   *   and `documentKeys` maps are visible to the next send and receive
   *   (`MeshNetworkAdapter` re-reads the keyring on every message, so
   *   `applyPairingToken` and friends take effect without a restart).
   *
   * - `{ storage }`: load the keyring once via the persistence adapter.
   *   When `storage.load()` resolves to `null`, the factory throws with
   *   a message pointing at the bootstrap helper in
   *   `@fairfox/polly/mesh/node`; we deliberately do not generate an
   *   identity silently.
   *
   * - `{ source }`: a synchronous function returning the current keyring.
   *   Called by `MeshNetworkAdapter` on every send and every receive.
   *   This is the shape that lets a long-lived mesh client recover from
   *   keyring updates written by a *different* process — wire the
   *   `source` to a cached object that a file watcher (or `readFileSync`
   *   on each call) refreshes from disk, and a freshly-paired peer
   *   becomes visible to the running adapter without any explicit
   *   notification path. See polly issue #100. */
  keyring: MeshKeyring | { storage: KeyringStorage } | { source: () => MeshKeyring };
  /** Optional Automerge-Repo storage adapter. Applications that want
   * durable local state pass an IndexedDB adapter in browsers or a
   * filesystem adapter in Node; omitting it keeps the Repo in-memory. */
  repoStorage?: StorageAdapterInterface;
  /** When `false`, signs but does not encrypt. Defaults to `true` — the
   * full $meshState posture where the server is off the data path. */
  encryptionEnabled?: boolean;
}

/**
 * Resolve the ICE server list a mesh client will use. The resolver wins
 * over a static `iceServers` list because the realistic deployment shape
 * is a consumer fetching short-lived TURN credentials per session — the
 * resolver is the integration point and a static list alongside it would
 * silently mask a broken credential flow. Exported for unit tests; the
 * production call site is inside {@link createMeshClient}.
 */
export async function resolveIceServers(
  rtc: CreateMeshClientOptions["rtc"]
): Promise<RTCIceServer[] | undefined> {
  if (rtc?.iceCredentialResolver) {
    return rtc.iceCredentialResolver();
  }
  return rtc?.iceServers;
}

/** Build the per-handle entry the polly#107 snapshot enrichment emits.
 * Combines the Repo-side `state` (the canonical lifecycle) with the
 * adapter-side wire timestamps. Extracted from the snapshot mapper to
 * keep the per-peer iteration under the cognitive-complexity ceiling. */
function buildHandleEntry(
  state: string,
  wire:
    | {
        lastSyncMessageOutAt: number | undefined;
        lastSyncMessageInAt: number | undefined;
        lastSyncMessageOutSize: number | undefined;
        lastSyncMessageOutType: string | undefined;
      }
    | undefined,
  syncStateView: PerPeerDocSyncView
): MeshClientHandleSnapshot {
  return {
    state,
    announcedToPeer: wire?.lastSyncMessageOutAt !== undefined,
    lastSyncMessageOutAt: wire?.lastSyncMessageOutAt,
    lastSyncMessageInAt: wire?.lastSyncMessageInAt,
    lastSyncMessageOutSize: wire?.lastSyncMessageOutSize,
    lastSyncMessageOutType: wire?.lastSyncMessageOutType,
    docSynchronizerExists: syncStateView.docSynchronizerExists,
    docSynchronizerKnowsPeer: syncStateView.docSynchronizerKnowsPeer,
    peerDocumentStatus: syncStateView.peerDocumentStatus,
  };
}

/** Per-(docId, peerId) view into Automerge's `CollectionSynchronizer`.
 * Built once per snapshot read and consulted from {@link buildHandleEntry}.
 * Structured this way so the docSynchronizer lookup is paid once per
 * docId, not once per (docId × peer). */
interface PerPeerDocSyncView {
  /** `true` iff Automerge's `CollectionSynchronizer.docSynchronizers`
   * has an entry for this documentId. A handle that exists in
   * `repo.handles` but has no corresponding `docSynchronizer` is the
   * `addDocument`-was-never-called fingerprint — Automerge's
   * NetworkSubsystem can never invoke `send` for it because no
   * synchronizer is wired up. */
  docSynchronizerExists: boolean;
  /** `true` iff the docSynchronizer for this documentId has registered
   * this peer in its internal peer list (`#peers`). `false` with
   * `docSynchronizerExists: true` is the symmetric polly#107 gap: the
   * synchronizer exists (`addDocument` ran) but `addPeer` was never
   * called for this peer on this doc — typically because the handle
   * was created AFTER `peer-candidate` fired and Automerge's
   * `addDocument`-iterates-known-peers path missed it. `undefined`
   * when no docSynchronizer exists. */
  docSynchronizerKnowsPeer: boolean | undefined;
  /** Automerge's `DocSynchronizer.peerStates[peerId]` — one of
   * `"unknown"`, `"has"`, `"unavailable"`, `"wants"`. `"unknown"`
   * with `lastSyncMessageOutAt` set means the local side sent its
   * opening handshake but never advanced past it; this is the
   * wedged-pair fingerprint #112 names. `undefined` when no
   * docSynchronizer exists OR when the synchronizer exists but
   * doesn't track this peer. */
  peerDocumentStatus: string | undefined;
}

/** Minimal structural shape we lift off Automerge's hidden
 * `Repo.synchronizer` / `CollectionSynchronizer` types. Kept narrow
 * so a future Automerge bump that renames a private rip doesn't
 * topple the snapshot path. */
interface SynchronizerStructural {
  docSynchronizers?: Record<
    string,
    {
      hasPeer?: (peerId: string) => boolean;
      peerStates?: Record<string, string>;
    }
  >;
}

const EMPTY_SYNC_VIEW: PerPeerDocSyncView = {
  docSynchronizerExists: false,
  docSynchronizerKnowsPeer: undefined,
  peerDocumentStatus: undefined,
};

/** Internal — exported for direct unit-test coverage of the #112
 * structural reader and snapshot wiring. Not part of the public API. */
export const __test__ = {
  buildSyncView: (
    synchronizer: SynchronizerStructural | undefined,
    docId: string,
    peerId: string
  ): PerPeerDocSyncView => buildSyncView(synchronizer, docId, peerId),
  EMPTY_SYNC_VIEW,
  getCollectionSynchronizer: (repo: Repo): SynchronizerStructural | undefined =>
    getCollectionSynchronizer(repo),
  enrichPeerSlot: (
    peer: ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["peers"][number],
    knownHandleIds: string[],
    repoHandles: Record<string, { state: unknown } | undefined>,
    synchronizer: SynchronizerStructural | undefined
  ): MeshClientPeerStateSnapshot["peers"][number] =>
    enrichPeerSlot(peer, knownHandleIds, repoHandles, synchronizer),
  // polly#124: revocation decision cores + already-pure diagnostics helpers,
  // pinned directly rather than through the integration-only factory.
  shouldReplaceRevocation,
  storeRevocationInto,
  revocationsMissingFromSummary,
  classifyIncomingRevocation,
  findLazyWrapperDocIdDuplicates,
  getReevaluateDocumentShare,
  installPolly107SyncReevaluation,
};

function getCollectionSynchronizer(repo: Repo): SynchronizerStructural | undefined {
  const sync = (repo as unknown as { synchronizer?: SynchronizerStructural }).synchronizer;
  return sync && typeof sync === "object" ? sync : undefined;
}

/** Build the per-(docId, peerId) docSynchronizer view for one peer. */
function buildSyncView(
  synchronizer: SynchronizerStructural | undefined,
  docId: string,
  peerId: string
): PerPeerDocSyncView {
  const docSync = synchronizer?.docSynchronizers?.[docId];
  if (!docSync) return EMPTY_SYNC_VIEW;
  let knowsPeer: boolean | undefined;
  try {
    knowsPeer = typeof docSync.hasPeer === "function" ? docSync.hasPeer(peerId) : undefined;
  } catch {
    knowsPeer = undefined;
  }
  let status: string | undefined;
  try {
    const states = docSync.peerStates;
    status = states && typeof states === "object" ? states[peerId] : undefined;
  } catch {
    status = undefined;
  }
  return {
    docSynchronizerExists: true,
    docSynchronizerKnowsPeer: knowsPeer,
    peerDocumentStatus: status,
  };
}

/** Stringify a Repo handle's `state` value for the enriched snapshot.
 * Handles whose machine snapshot returns an object collapse to a
 * coerced string; in practice polly's $meshState always lands on a
 * leaf string. Returns `"unknown"` when the handle entry itself is
 * undefined. */
function stringifyHandleState(handle: { state: unknown } | undefined): string {
  if (handle === undefined) return "unknown";
  return typeof handle.state === "string" ? handle.state : String(handle.state ?? "unknown");
}

/** Enrich one peer's slot view with the per-handle Repo×adapter merge
 * polly#107 item 7 specifies. Pulled out of the snapshot factory so the
 * outer factory stays under the cognitive-complexity ceiling and so
 * the per-iteration code is testable in isolation. */
function enrichPeerSlot(
  peer: ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["peers"][number],
  knownHandleIds: string[],
  repoHandles: Record<string, { state: unknown } | undefined>,
  synchronizer: SynchronizerStructural | undefined
): MeshClientPeerStateSnapshot["peers"][number] {
  if (!peer.slot) {
    return { ...peer, slot: undefined } as MeshClientPeerStateSnapshot["peers"][number];
  }
  const peerIdString = peer.peerId as unknown as string;
  const enriched: Record<string, MeshClientHandleSnapshot> = {};
  for (const docId of knownHandleIds) {
    enriched[docId] = buildHandleEntry(
      stringifyHandleState(repoHandles[docId]),
      peer.slot.handles[docId],
      buildSyncView(synchronizer, docId, peerIdString)
    );
  }
  for (const docId of Object.keys(peer.slot.handles)) {
    if (enriched[docId]) continue;
    enriched[docId] = buildHandleEntry(
      "unknown",
      peer.slot.handles[docId],
      buildSyncView(synchronizer, docId, peerIdString)
    );
  }
  return { ...peer, slot: { ...peer.slot, handles: enriched } };
}

/** Lift the synchronizer's `reevaluateDocumentShare` method off a Repo
 * through a narrowed structural accessor.
 * `synchronizer.reevaluateDocumentShare` is `@hidden` on the Automerge
 * type, so we reach for it tolerantly — the worst case is the
 * polly#107 fix silently degrades to the pre-fix shape, which the
 * observability layer still surfaces clearly. */
function getReevaluateDocumentShare(repo: Repo): (() => Promise<void>) | undefined {
  const sync = (
    repo as unknown as {
      synchronizer?: { reevaluateDocumentShare?: () => Promise<void> };
    }
  ).synchronizer;
  const fn = sync?.reevaluateDocumentShare;
  if (typeof fn !== "function" || sync === undefined) return undefined;
  return () => fn.call(sync);
}

/** Build the {@link MeshStateModuleDiagnostics} block surfaced on
 * every {@link MeshClient.getPeerStateSnapshot}. Reads the module
 * state in one place so both snapshot construction sites (the
 * pre-adapter early-out and the main path) stay identical. */
function buildMeshStateModuleDiagnostics(): MeshStateModuleDiagnostics {
  const lazyWrappers = getLazyWrappers();
  return {
    moduleId: getMeshStateModuleId(),
    configured: isMeshStateConfigured(),
    lastConfiguredRepoPeerId: getLastConfiguredRepoPeerId(),
    wasResolved: wasMeshStateResolved(),
    lazyInvocations: getLazyInvocations(),
    lazyReachedRepo: getLazyReachedRepo(),
    lastLoadedRejection: getLastLoadedRejection(),
    storageOpenError: getStorageOpenError(),
    lazyWrappers,
    lazyWrapperDuplicateDocIds: findLazyWrapperDocIdDuplicates(lazyWrappers),
  };
}

/** Polly#107 post-v0.60 instrumentation. Walks the lazy-wrapper log
 * and groups records by `docId`; emits one entry per `docId` that
 * appears in more than one record. Surfaces the "17 wrappers / 16
 * `repo.handles`" off-by-one shape that the v0.60.0 single-tab
 * fingerprint flagged — typically two distinct `$mesh*` consumer
 * call sites whose logical keys hash to the same Automerge
 * `DocumentId`, or the same logical key invoked from two consumers
 * during pre-warm before either factory's `repo.import` committed
 * the handle. The snapshot can paste this verbatim; an empty array
 * means the wrapper-to-handle accounting is one-to-one. */
export interface MeshStateLazyWrapperDocIdDuplicate {
  /** The `DocumentId` that more than one factory invocation
   * resolved to. */
  docId: string;
  /** Distinct logical keys that derived to this same `DocumentId`.
   * Length 1 means the same key was registered twice; length > 1
   * means two different keys hashed to the same id (a SHA-512-prefix
   * collision in {@link deriveDocumentId}, vanishingly unlikely but
   * detected for completeness). */
  keys: string[];
  /** Total number of records in the lazy-wrapper log that resolved
   * to this `DocumentId`. Typically 2 for a same-key double-call. */
  recordCount: number;
}

function findLazyWrapperDocIdDuplicates(
  records: readonly MeshStateLazyWrapperRecord[]
): MeshStateLazyWrapperDocIdDuplicate[] {
  const byDocId = new Map<string, { keys: Set<string>; count: number }>();
  for (const record of records) {
    let entry = byDocId.get(record.docId);
    if (!entry) {
      entry = { keys: new Set(), count: 0 };
      byDocId.set(record.docId, entry);
    }
    entry.keys.add(record.key);
    entry.count++;
  }
  const duplicates: MeshStateLazyWrapperDocIdDuplicate[] = [];
  for (const [docId, entry] of byDocId) {
    if (entry.count > 1) {
      duplicates.push({ docId, keys: [...entry.keys], recordCount: entry.count });
    }
  }
  return duplicates;
}

// ─── RFC-043 revocation decision cores ───────────────────────────────────────
// Extracted from the createMeshClient closures so the load-bearing logic — the
// last-write-wins store guard, the gossip diff, and the incoming-revocation
// classification — is unit-testable in isolation (polly#124). The closures
// below delegate to these; the I/O (decode/apply/emit/send) stays in the
// closure.

type StoredRevocation = { bytes: Uint8Array; entry: RevocationSummaryEntry };

/** Whether an incoming revocation should overwrite what the store already
 * holds for that revoked peer. The De Morgan dual of the original skip-guard
 * `existing && existing.issuedAt >= record.issuedAt`: store when there is no
 * existing record, or the incoming one is strictly newer. Equal `issuedAt`
 * keeps the existing record (last-write-wins on a strict newer-than). */
function shouldReplaceRevocation(
  existing: StoredRevocation | undefined,
  record: RevocationRecord
): boolean {
  return existing === undefined || record.issuedAt > existing.entry.issuedAt;
}

function storeRevocationInto(
  store: Map<string, StoredRevocation>,
  record: RevocationRecord,
  bytes: Uint8Array
): void {
  const existing = store.get(record.revokedPeerId);
  if (!shouldReplaceRevocation(existing, record)) return;
  store.set(record.revokedPeerId, {
    bytes,
    entry: {
      revokedPeerId: record.revokedPeerId,
      issuerPeerId: record.issuerPeerId,
      issuedAt: record.issuedAt,
    },
  });
}

/** The encoded revocations the local store holds that the remote peer's summary
 * does not — the bytes to push so both sides converge to the union after one
 * round trip. Membership is keyed by `revokedPeerId`. */
function revocationsMissingFromSummary(
  store: Map<string, StoredRevocation>,
  summary: readonly RevocationSummaryEntry[]
): Uint8Array[] {
  const remoteKeys = new Set(summary.map((entry) => entry.revokedPeerId));
  const missing: Uint8Array[] = [];
  for (const stored of store.values()) {
    if (remoteKeys.has(stored.entry.revokedPeerId)) continue;
    missing.push(stored.bytes);
  }
  return missing;
}

/** Classify an incoming revocation. Branch order is load-bearing: a
 * self-targeted record is `"self"` even if it also appears in `revokedPeers`. */
function classifyIncomingRevocation(
  record: RevocationRecord,
  localPeerId: string,
  revokedPeers: ReadonlySet<string>
): "self" | "duplicate" | "apply" {
  if (record.revokedPeerId === localPeerId) return "self";
  if (revokedPeers.has(record.revokedPeerId)) return "duplicate";
  return "apply";
}

/** Install the polly#107 peer-candidate hook on a freshly-constructed
 * mesh stack. Hides the falsification-gate branch behind a single call
 * so the outer factory's complexity score stays under the ceiling. */
function installPolly107SyncReevaluation(networkAdapter: MeshNetworkAdapter, repo: Repo): void {
  const disable = typeof process !== "undefined" && process.env?.["POLLY_107_DISABLE_FIX"] === "1";
  if (disable) return;
  const reevaluate = getReevaluateDocumentShare(repo);
  if (!reevaluate) return;
  networkAdapter.on("peer-candidate", () => {
    void reevaluate().catch(() => {
      // Synchronizer errors are observable through
      // getPeerStateSnapshot; suppressing here keeps a single bad doc
      // from taking down the whole peer-candidate path.
    });
  });
}

/** Per-peer per-handle enrichment polly#107 adds on top of the
 * {@link MeshWebRTCAdapter} snapshot. `state` and `announcedToPeer`
 * come from the Repo side (which the adapter cannot see); the wire
 * timestamps come from the adapter's per-slot bookkeeping. */
export interface MeshClientHandleSnapshot {
  /** The local handle's lifecycle state — `"ready"`, `"loading"`,
   * `"unavailable"`, etc. — as reported by the Repo. `"unknown"` is
   * stamped when the wire has seen a sync message for a documentId
   * the local repo hasn't constructed a handle for yet (a remote peer
   * announcing a doc we haven't touched). */
  state: string;
  /** True iff polly's network adapter has dispatched at least one
   * outbound sync message for this document to this peer. Equivalent
   * to `lastSyncMessageOutAt !== undefined` but named for the
   * diagnostic question polly#107 asks the snapshot to answer:
   * "has Automerge's NetworkSubsystem told this peer about this
   * handle?". The failing-shape this ticket reports is precisely
   * the case where every entry has `state: "ready"` and
   * `announcedToPeer: false`. */
  announcedToPeer: boolean;
  /** `performance.now()` of the most recent outbound sync message for
   * this document to this peer. `undefined` until first send. */
  lastSyncMessageOutAt: number | undefined;
  /** `performance.now()` of the most recent inbound message dispatched
   * upward for this document from this peer. `undefined` until first
   * receive. */
  lastSyncMessageInAt: number | undefined;
  /** Byte length of the most recent outbound message. */
  lastSyncMessageOutSize: number | undefined;
  /** Type field of the most recent outbound message — typically
   * `"sync"` after handshake, `"request"` while the local side is
   * asking. */
  lastSyncMessageOutType: string | undefined;
  /** #112 diagnostic. `true` iff Automerge's `CollectionSynchronizer`
   * has a `docSynchronizer` entry for this document. A handle in
   * `repo.handles` with no docSynchronizer is the
   * `addDocument`-never-ran fingerprint: Automerge's NetworkSubsystem
   * can never call `send` for it because no synchronizer is wired up. */
  docSynchronizerExists: boolean;
  /** #112 diagnostic. `true` iff the docSynchronizer for this document
   * has this peer in its internal peer list. `false` with
   * `docSynchronizerExists: true` is the symmetric polly#107 gap —
   * the synchronizer exists but `addPeer` was never invoked on it for
   * this peer, typically because the handle was created AFTER
   * `peer-candidate` fired and Automerge's
   * `addDocument`-iterates-peers path missed it. `undefined` when no
   * docSynchronizer exists. */
  docSynchronizerKnowsPeer: boolean | undefined;
  /** #112 diagnostic. Automerge's
   * `DocSynchronizer.peerStates[peerId]` — one of `"unknown"`,
   * `"has"`, `"unavailable"`, `"wants"`. `"unknown"` together with a
   * set `lastSyncMessageOutAt` is the wedged-pair fingerprint this
   * ticket names: the opening handshake left the wire but the
   * synchronizer never learned whether the remote has the doc, so
   * `generateSyncMessage` quiesces. `undefined` when no
   * docSynchronizer exists OR when the synchronizer does not track
   * this peer. */
  peerDocumentStatus: string | undefined;
}

/** Polly#107 H5 diagnostics: surfaces the `mesh-state` module
 * instance identity so a single snapshot read tells the operator
 * whether the consumer's `$meshState` wrappers are resolving against
 * the same module instance `createMeshClient` configured. A mismatch
 * here IS the bundle-time module duplication bug. */
export interface MeshStateModuleDiagnostics {
  /** The id stamped at import time on the `mesh-state` module
   * instance THIS mesh client was constructed against. Compare to
   * the id seen at the `$meshState` call site (also importable as
   * `MESH_STATE_MODULE_ID` from `@fairfox/polly/mesh`). Two different
   * ids means the consumer is reaching a duplicated copy of
   * `mesh-state.ts` — wrappers register handles against a Repo this
   * mesh client never saw. */
  moduleId: string;
  /** `true` iff THIS module instance has a configured `defaultRepo`.
   * In the H5 scenario, this is `true` for the mesh-client-side
   * snapshot (because `createMeshClient` always calls
   * `configureMeshState` on the module it imports), but the same
   * field read from the consumer's `$meshState` call site would
   * be `false`. */
  configured: boolean;
  /** `peerId` of the most recent Repo wired through
   * `configureMeshState` against THIS module instance. Compared to
   * `client.repo.peerId` and the consumer's wrappers' resolved Repo
   * tells the full story. */
  lastConfiguredRepoPeerId: string | undefined;
  /** `true` if any `$meshState`-family wrapper has been called
   * against THIS module instance at any point. The polly#107 H5
   * fingerprint pair: `configured: true, wasResolved: false` on
   * the mesh-client-side snapshot (the wrappers never reached us);
   * the consumer's wrapper code reading the same field from THEIR
   * `$meshState` import would see `configured: false, wasResolved:
   * true` (they're using a module instance no mesh client ever
   * configured). */
  wasResolved: boolean;
  /** Polly#107 post-H5 instrumentation. Count of `$meshState`-family
   * lazy factory invocations since module load. Once the consumer's
   * pre-warm pass completes, this equals the number of distinct
   * `$mesh*` wrappers whose handles the loader actually tried to
   * resolve. Compared to {@link lazyReachedRepo}: gap = throws
   * before any Repo work. */
  lazyInvocations: number;
  /** Polly#107 post-H5 instrumentation. Count of factory invocations
   * that reached the Repo subsystem (`repo.handles[...]`, `repo.find`
   * or `repo.import`) before returning or throwing. If
   * {@link lazyInvocations} is N and this is N, every wrapper
   * touched the Repo — any missing handles are downstream of Repo
   * registration. If this is < N, the gap is the call site to
   * instrument next. */
  lazyReachedRepo: number;
  /** Polly#107 post-H5 instrumentation. Breadcrumb for the most
   * recent rejection from a `$meshState`-family `loaded` promise
   * (or its factory). Captured even when the consumer's wrapper
   * never awaits `loaded` and the rejection would otherwise vanish
   * silently. `undefined` means no rejection has escaped any
   * wrapper on THIS module instance since module load. */
  lastLoadedRejection: MeshStateLoadedRejectionBreadcrumb | undefined;
  /** Polly#107 post-v0.60 instrumentation. Populated when a storage
   * read inside `buildHandleFactory` exceeds the internal 5s
   * timeout — i.e. `cached.whenReady(...)` or
   * `repo.storageSubsystem.loadDoc(...)` hung. Names the operation,
   * the document id under attempt, the elapsed time, and a
   * pre-formatted message ready to paste into a ticket. The v0.60.0
   * fingerprint diagnosed "factories hung mid-await, not throwing"
   * indirectly; this field surfaces the same shape within seconds
   * and in one read. `undefined` means no storage timeout has
   * occurred since module load. */
  storageOpenError: MeshStateStorageOpenError | undefined;
  /** Polly#107 post-v0.59 instrumentation. Per-factory-invocation
   * structured log — one record per `$mesh*` wrapper's lazy handle
   * factory call, ring-buffered at 64 entries. Each row names the
   * exit path (`returned-cached`, `loaded-from-storage`,
   * `seeded-and-imported`, `threw`) and the synchronous peek at
   * `repo.handles[docId]` taken in the factory's `finally`. The
   * v0.59.0 fingerprint had `lazyInvocations === lazyReachedRepo`
   * and no `lastLoadedRejection`; this field disambiguates which
   * exit path each "successful" invocation actually took and
   * whether the Repo registered the handle in spite of the lack of
   * a thrown error. The smoking gun for H-Q1 is rows with
   * `exitReason: "seeded-and-imported"` and
   * `handleRegistered: false`. */
  lazyWrappers: MeshStateLazyWrapperRecord[];
  /** Polly#107 post-v0.60 instrumentation. One entry per
   * `DocumentId` that appears in more than one
   * {@link lazyWrappers} record — the shape behind the v0.60.0
   * single-tab fingerprint's "17 wrappers / 16 `repo.handles`"
   * off-by-one. Empty when wrapper-to-handle accounting is
   * one-to-one, populated when two factory invocations resolved to
   * the same `DocumentId` (most commonly the same logical key
   * registered from two consumer call sites during pre-warm). */
  lazyWrapperDuplicateDocIds: MeshStateLazyWrapperDocIdDuplicate[];
}

/** The mesh client's enriched per-peer state snapshot. Mirrors the
 * underlying {@link MeshWebRTCAdapter.getPeerStateSnapshot} shape but
 * replaces the slot's `handles` map with the Repo-enriched view
 * polly#107 adds. */
export interface MeshClientPeerStateSnapshot {
  localPeerId: string;
  knownPeerIds: string[];
  presentPeerIds: string[];
  sweep: ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["sweep"];
  peers: Array<
    Omit<ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["peers"][number], "slot"> & {
      slot:
        | undefined
        | (Omit<
            NonNullable<
              ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["peers"][number]["slot"]
            >,
            "handles"
          > & {
            handles: Record<string, MeshClientHandleSnapshot>;
          });
    }
  >;
  /** polly#107 H5 diagnostics. See {@link MeshStateModuleDiagnostics}. */
  meshStateModule: MeshStateModuleDiagnostics;
  /** Count of handles known to the Repo this client owns. Compared
   * to the count the consumer's `$meshState` wrappers should have
   * registered: a mismatch (e.g. consumer pre-warmed 14 wrappers,
   * snapshot reports 1) confirms the H5 module-duplication
   * fingerprint without needing a separate read. */
  repoHandleCount: number;
  /** All handle ids the Repo this client owns currently caches.
   * Together with `repoHandleCount` and `meshStateModule.moduleId`,
   * this answers "did the consumer's wrappers land their handles in
   * THIS Repo?" in one read. */
  repoHandleIds: string[];
}

/** Handle returned by {@link createMeshClient}. */
export interface MeshClient {
  /** The Automerge Repo. `$meshState` has already been configured against
   * this repo, so primitives just work — but the repo is exposed in case
   * the application needs it directly (server-side cron, bulk exports,
   * migration tools). */
  repo: Repo;
  /** The current keyring. Reads through the same live source the network
   * adapter uses, so the value always reflects the latest snapshot —
   * including changes introduced after construction via in-place mutation
   * or a `{ source }` callback. Applications can inspect or mutate the
   * returned object (add authorised peers, apply revocations) and the
   * next mesh message sees the change. */
  readonly keyring: MeshKeyring;
  /** The signalling client. Exposed for applications that need to hook
   * lifecycle events or send custom signalling payloads. */
  signaling: MeshSignalingClient;
  /** The WebRTC network adapter. Exposed for advanced use (blob store
   * wiring, peer-connection introspection). */
  networkAdapter: MeshNetworkAdapter;
  /** The underlying WebRTC adapter wrapped by {@link networkAdapter}. */
  webrtcAdapter: MeshWebRTCAdapter;
  /** Re-evaluate every peer currently in the signalling roster and
   * dial the ones the keyring now authorises that this client has not
   * already dialled. Equivalent to
   * {@link MeshWebRTCAdapter.refreshKnownPeers}; the periodic sweep
   * inside the WebRTC adapter calls the same code path, so consumers
   * only need this helper when they want to skip the wait between
   * sweeps after applying a pair token. Polly issue #103 — the path
   * the sweep was added to close — is the canonical use case. */
  refreshKnownPeers(): void;
  /** Snapshot of the mesh client's per-peer state — keyring
   * membership, signalling presence, per-slot SDP / ICE /
   * connectionState / data-channel state, queued-send / queued-ICE
   * depth, and per-peer per-handle sync state (state, announcedToPeer,
   * last sync message in/out). Plain data, safe to log or render.
   * Exists so a consumer harness can answer "is the mesh layer in a
   * known good state, AND has Automerge actually announced every
   * local handle to every connected peer" without instrumenting polly
   * internals. Polly issue #103 item 7; polly#107 item 7 added the
   * per-handle enrichment that this method overlays on top of the
   * underlying {@link MeshWebRTCAdapter} snapshot. */
  getPeerStateSnapshot(): MeshClientPeerStateSnapshot;
  /** Refresh every active peer slot's transport-level summary —
   * selected ICE candidate pair, SCTP retransmission counters, last
   * data-channel error — and populate it into the next
   * {@link getPeerStateSnapshot}. Walks {@link RTCPeerConnection.getStats}
   * once per peer, so it isn't free; consumers that want continuous
   * visibility should call this on a polling cadence the cost can
   * absorb. Polly issue #105 item 7. */
  refreshTransportStats(): Promise<void>;
  /** Force the Automerge synchronizer to re-evaluate every (handle ×
   * peer) pair and `beginSync` for any pair that should be syncing
   * but isn't. Called automatically on `peer-candidate` post-#107;
   * exposed for explicit invocation by harnesses that need to assert
   * the fix is engaged or that want a deterministic checkpoint after
   * post-construction handle additions.
   *
   * Resolves once the synchronizer's internal `Promise.allSettled`
   * over per-doc reevaluations resolves. Idempotent: if every pair is
   * already syncing this is a no-op. Polly issue #107 item 7. */
  reevaluateAllSync(): Promise<void>;
  /**
   * Issue a revocation against `targetPeerId` (RFC-043). The local
   * keyring is mutated to drop the target immediately; the encoded
   * signed record is broadcast to every currently-connected peer, who
   * apply it through the same path on receipt. Past contributions from
   * the revoked peer stay in any document they already merged into;
   * future writes are dropped at every peer's adapter once they
   * receive the revocation.
   *
   * Resolves once the local keyring has been mutated and the broadcast
   * has been handed to the base adapter. Delivery to disconnected
   * peers happens via the reconnect re-broadcast scheduled by the
   * next RFC-043 PR.
   */
  revokePeer(targetPeerId: string, reason?: string): Promise<void>;
  /**
   * If a remote peer has issued a revocation that names the local
   * peer as its target, this field carries the parsed
   * {@link RevocationRecord}. Applications observe it to render a
   * "this device has been revoked by your other device on date X"
   * UX. The mesh continues to receive other peers' messages so the
   * application can surface further detail (more revocations from
   * the same issuer, etc.); only this device's outbound writes are
   * suppressed.
   *
   * Undefined while no self-targeted revocation has been seen.
   */
  readonly selfRevocation: RevocationRecord | undefined;
  /** Close the signalling WebSocket, tear down every RTCPeerConnection,
   * and shut the Repo cleanly. Idempotent. */
  close(): Promise<void>;
}

/**
 * Construct a fully-wired mesh client. Resolves once the signalling
 * connection is open and the Repo is ready to mutate documents; WebRTC
 * peer connections negotiate asynchronously in the background.
 */
export async function createMeshClient(options: CreateMeshClientOptions): Promise<MeshClient> {
  const keyringSource = await resolveKeyringSource(options.keyring);
  const keyring = keyringSource();
  const encryptionEnabled = options.encryptionEnabled ?? true;

  // A mesh keyring must carry the per-Repo document key used by
  // MeshNetworkAdapter's encryption layer. We fail loud rather than
  // silently disable encryption when encryptionEnabled is true.
  if (encryptionEnabled && !keyring.documentKeys.has(DEFAULT_MESH_KEY_ID)) {
    throw new Error(
      `createMeshClient: encryption is enabled but the keyring has no document key for "${DEFAULT_MESH_KEY_ID}". Bootstrap or apply a pairing token that carries the document key before connecting.`
    );
  }

  // Seed the WebRTC adapter with the keyring's current `knownPeers`
  // snapshot AND wire it to the same live keyring source the crypto
  // layer uses. The snapshot is kept for the legacy captured-set path
  // (consumers wiring MeshWebRTCAdapter directly without a source) and
  // as a "first sweep" hint; the live source is what closes polly
  // issue #103, where a long-lived daemon's keyring gains entries
  // through `applyPairingToken` after the adapter is already up and
  // the captured Set would otherwise never learn about them. The
  // crypto layer (MeshNetworkAdapter) reads the same source on every
  // send/receive — see mesh-network-adapter.ts for the matching
  // contract.
  const knownPeerIds = [...keyring.knownPeers.keys()].filter(
    (id) => id !== options.signaling.peerId
  );

  // The resolver wins when both are set. Failure here surfaces as a
  // create-time rejection rather than a silent fall-through to STUN-only,
  // which would mask broken credential plumbing until a real symmetric
  // NAT user reported "can't connect".
  const resolvedIceServers = await resolveIceServers(options.rtc);

  const webrtcAdapterOptions: MeshWebRTCAdapterOptions = {
    signaling: undefined as unknown as MeshSignalingClient, // wired after signaling construction
    peerId: options.signaling.peerId,
    knownPeerIds,
    keyringSource,
    ...(resolvedIceServers !== undefined && { iceServers: resolvedIceServers }),
    ...(options.rtc?.iceTransportPolicy !== undefined && {
      iceTransportPolicy: options.rtc.iceTransportPolicy,
    }),
    ...(options.rtc?.iceRelayEnforcement !== undefined && {
      iceRelayEnforcement: options.rtc.iceRelayEnforcement,
    }),
    ...(options.rtc?.dataChannelLabel !== undefined && {
      dataChannelLabel: options.rtc.dataChannelLabel,
    }),
    ...(options.rtc?.RTCPeerConnection !== undefined && {
      RTCPeerConnection: options.rtc.RTCPeerConnection,
    }),
    ...(options.rtc?.knownPeersRefreshIntervalMs !== undefined && {
      knownPeersRefreshIntervalMs: options.rtc.knownPeersRefreshIntervalMs,
    }),
    ...(options.rtc?.syncYieldEnabled !== undefined && {
      syncYieldEnabled: options.rtc.syncYieldEnabled,
    }),
    ...(options.rtc?.syncFragmentChunkSizeOverride !== undefined && {
      syncFragmentChunkSizeOverride: options.rtc.syncFragmentChunkSizeOverride,
    }),
  };

  // The signalling client needs a handleSignal callback, but that callback
  // lives on the WebRTC adapter — which itself wants a reference to the
  // signalling client for sending answers. Break the cycle by letting the
  // signalling client's callbacks reach the adapter through a closure
  // over `webrtcAdapter`, which is assigned immediately below. The same
  // closure pattern wires the peer-discovery callbacks
  // (onPeersPresent / onPeerJoined / onPeerLeft) through to the adapter's
  // dispatch methods.
  let webrtcAdapter: MeshWebRTCAdapter | undefined;
  const signaling = new MeshSignalingClient({
    url: options.signaling.url,
    peerId: options.signaling.peerId,
    ...(options.signaling.WebSocket !== undefined && { WebSocket: options.signaling.WebSocket }),
    ...(options.signaling.onError !== undefined && { onError: options.signaling.onError }),
    ...(options.signaling.onCustomFrame !== undefined && {
      onCustomFrame: options.signaling.onCustomFrame,
    }),
    onSignal: (fromPeerId, payload) => {
      webrtcAdapter?.handleSignal(fromPeerId, payload);
    },
    onPeersPresent: (peerIds) => {
      webrtcAdapter?.handlePeersPresent(peerIds);
    },
    onPeerJoined: (peerId) => {
      webrtcAdapter?.handlePeerJoined(peerId);
    },
    onPeerLeft: (peerId) => {
      webrtcAdapter?.handlePeerLeft(peerId);
    },
  });

  webrtcAdapterOptions.signaling = signaling;
  webrtcAdapter = new MeshWebRTCAdapter(webrtcAdapterOptions);

  // RFC-043 state: the set of peer ids with an active mesh connection
  // (the broadcast target for revocations), the local peer's
  // self-targeted revocation if any peer has issued one, and the
  // local revocation store (keyed by revokedPeerId) that drives the
  // peer-candidate summary gossip in PR 3.
  const connectedPeerIds = new Set<PeerId>();
  let selfRevocation: RevocationRecord | undefined;
  const localPeerId = options.signaling.peerId;
  const revocationStore = new Map<string, { bytes: Uint8Array; entry: RevocationSummaryEntry }>();

  function storeRevocation(record: RevocationRecord, bytes: Uint8Array): void {
    storeRevocationInto(revocationStore, record, bytes);
  }

  const handleRevocationControl = (body: Uint8Array, senderId: string): void => {
    const keyring = keyringSource();
    let record: RevocationRecord;
    try {
      record = decodeRevocation(body, keyring);
    } catch (err) {
      const reason =
        err instanceof RevocationError
          ? err.code
          : err instanceof Error
            ? err.message
            : String(err);
      emitMeshDiagnostic({ kind: "revoke:rejected", senderId, reason });
      return;
    }
    switch (classifyIncomingRevocation(record, localPeerId, keyring.revokedPeers)) {
      case "self":
        // RFC-043: self-targeted revocations do not silence the
        // receiving peer's keyring; the application binds to the
        // diagnostic + the selfRevocation field on MeshClient to surface
        // the "you have been revoked" UX.
        selfRevocation = record;
        emitMeshDiagnostic({
          kind: "revoke:self-targeted",
          issuerId: record.issuerPeerId,
          ...(record.reason !== undefined && { reason: record.reason }),
          issuedAt: record.issuedAt,
        });
        return;
      case "duplicate":
        // Already known. Keep the blob so this peer can gossip it
        // forward (the latest issuedAt wins inside storeRevocation).
        storeRevocation(record, body);
        emitMeshDiagnostic({
          kind: "revoke:duplicate",
          revokedPeerId: record.revokedPeerId,
          issuerId: record.issuerPeerId,
        });
        return;
      case "apply":
        applyRevocation(record, keyring);
        storeRevocation(record, body);
        emitMeshDiagnostic({ kind: "revoke:applied", revokedPeerId: record.revokedPeerId });
        return;
    }
  };

  const handleRevocationSummary = (body: Uint8Array, senderId: string): void => {
    let summary: RevocationSummaryEntry[];
    try {
      summary = decodeRevocationSummary(body);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "revoke:rejected",
        senderId,
        reason: err instanceof Error ? err.message : String(err),
      });
      return;
    }
    // Push every revocation the local peer holds that the remote
    // peer's summary does not. The remote runs the same algorithm
    // against this peer's summary, so both sides converge to the
    // union after one round trip.
    const senderPeerId = senderId as PeerId;
    for (const bytes of revocationsMissingFromSummary(revocationStore, summary)) {
      networkAdapter.sendControlMessage(MESH_CONTROL_TYPE.Revocation, bytes, [senderPeerId]);
    }
  };

  const networkAdapter = new MeshNetworkAdapter({
    base: webrtcAdapter,
    keyringSource,
    encryptionEnabled,
    onControlMessage: (tag, body, senderId) => {
      if (tag === MESH_CONTROL_TYPE.Revocation) {
        handleRevocationControl(body, senderId);
      } else if (tag === MESH_CONTROL_TYPE.RevocationSummary) {
        handleRevocationSummary(body, senderId);
      }
    },
  });

  function sendSummaryTo(peerId: PeerId): void {
    const entries = [...revocationStore.values()].map((stored) => stored.entry);
    const body = encodeRevocationSummary(entries);
    networkAdapter.sendControlMessage(MESH_CONTROL_TYPE.RevocationSummary, body, [peerId]);
  }

  // Maintain the connected-peer set from the adapter's lifecycle events.
  // The set drives revokePeer's broadcast target list; the peer-candidate
  // hook also kicks off the revocation-summary gossip so a peer that was
  // offline at issue-time picks the revocation up on reconnect.
  networkAdapter.on("peer-candidate", (event: { peerId: PeerId }) => {
    connectedPeerIds.add(event.peerId);
    try {
      sendSummaryTo(event.peerId);
    } catch (err) {
      emitMeshDiagnostic({
        kind: "revoke:rejected",
        senderId: event.peerId,
        reason: `summary-send-failed: ${err instanceof Error ? err.message : String(err)}`,
      });
    }
  });
  networkAdapter.on("peer-disconnected", (event: { peerId: PeerId }) => {
    connectedPeerIds.delete(event.peerId);
  });

  // The Repo's peerId MUST match the mesh peer id we signed the keyring
  // against. Automerge would otherwise auto-generate a random "peer-xxxxx"
  // identifier, and `MeshNetworkAdapter`'s outgoing envelope would carry
  // that auto-id as its `senderId` — a value the remote keyring has never
  // seen and cannot look up in `knownPeers`. Every message would then fail
  // signature verification silently, and no `$meshState` sync would ever
  // apply.
  const repo = new Repo({
    network: [networkAdapter],
    peerId: options.signaling.peerId as unknown as PeerId,
    ...(options.repoStorage !== undefined && { storage: options.repoStorage }),
  });

  configureMeshState(repo);

  // polly#107 — on peer-candidate, force the synchronizer to
  // re-evaluate every (handle × peer) pair so any handle whose
  // `addDocument`/`addPeer` ordering race left it un-synced for this
  // peer gets `beginSync` invoked synchronously after the peer is
  // registered. The default Automerge flow IS supposed to handle this
  // through the `addPeer`-iterates-docSynchronizers and
  // `addDocument`-iterates-#peers cross-paths, but the polly#107
  // failing-shape evidence (fourteen pre-warmed handles, peer-candidate
  // fires, firstOutboundSendAt stays `(none)`) shows that path leaves
  // a gap in the realistic case. `reevaluateDocumentShare` walks every
  // docSynchronizer and starts a `beginSync` for every peer that
  // should be syncing but isn't — idempotent for handles that already
  // started, load-bearing for handles that didn't.
  //
  // Falsification gate (POLLY_107_DISABLE_FIX=1): skip the
  // re-evaluation so the pre-fix shape is preserved. The polly#107
  // example asserts that pre-fix-emulated runs produce the named
  // failure "Automerge never invoked NetworkAdapter.send despite N
  // handles in repo and inbound messages received", which is exactly
  // the production shape the ticket reports.
  installPolly107SyncReevaluation(networkAdapter, repo);

  await signaling.connect();

  return {
    repo,
    get keyring(): MeshKeyring {
      return keyringSource();
    },
    signaling,
    networkAdapter,
    webrtcAdapter,
    refreshKnownPeers: () => {
      webrtcAdapter?.refreshKnownPeers();
    },
    getPeerStateSnapshot: () => {
      // The closure-captured `webrtcAdapter` is assigned synchronously
      // before this object is returned, so the optional chain is
      // belt-and-braces against future construction reorderings.
      if (!webrtcAdapter) {
        return {
          localPeerId: options.signaling.peerId,
          knownPeerIds: [],
          presentPeerIds: [],
          sweep: {
            enabled: false,
            intervalMs: 0,
            runCount: 0,
            lastRunAt: undefined,
          },
          peers: [],
          meshStateModule: buildMeshStateModuleDiagnostics(),
          repoHandleCount: Object.keys(repo.handles).length,
          repoHandleIds: Object.keys(repo.handles),
        };
      }
      const base = webrtcAdapter.getPeerStateSnapshot() as ReturnType<
        MeshWebRTCAdapter["getPeerStateSnapshot"]
      >;
      // Enrich the adapter view with Repo-side handle state so the
      // polly#107 item 7 contract is observable in one place. The
      // adapter sees only the wire path; the Repo's `handles` map
      // owns the `state` (ready / loading / unavailable) and is the
      // canonical answer to "what handles does the local replica
      // hold?". Combining them produces "for each handle this replica
      // holds, has Automerge announced it to this peer yet?". The
      // failure shape polly#107 reports is precisely the case where
      // every entry in `repo.handles` is `ready` and every
      // corresponding `slot.handles[docId].lastSyncMessageOutAt` is
      // `undefined`.
      const repoHandles = repo.handles as unknown as Record<string, { state: unknown } | undefined>;
      const knownHandleIds = Object.keys(repoHandles);
      const synchronizer = getCollectionSynchronizer(repo);
      const enrichedPeers: MeshClientPeerStateSnapshot["peers"] = base.peers.map((peer) =>
        enrichPeerSlot(peer, knownHandleIds, repoHandles, synchronizer)
      );
      const out: MeshClientPeerStateSnapshot = {
        localPeerId: base.localPeerId,
        knownPeerIds: base.knownPeerIds,
        presentPeerIds: base.presentPeerIds,
        sweep: base.sweep,
        peers: enrichedPeers,
        meshStateModule: buildMeshStateModuleDiagnostics(),
        repoHandleCount: knownHandleIds.length,
        repoHandleIds: knownHandleIds,
      };
      return out;
    },
    reevaluateAllSync: async () => {
      const reevaluate = getReevaluateDocumentShare(repo);
      if (!reevaluate) return;
      await reevaluate();
    },
    refreshTransportStats: async () => {
      if (!webrtcAdapter) return;
      await webrtcAdapter.refreshAllTransportStats();
    },
    revokePeer: async (targetPeerId, reason) => {
      const keyring = keyringSource();
      const record = createRevocation({
        issuer: keyring.identity,
        issuerPeerId: localPeerId,
        revokedPeerId: targetPeerId,
        ...(reason !== undefined && { reason }),
      });
      const bytes = encodeRevocation(record, keyring.identity);
      // Apply locally first so the issuer's adapter starts dropping
      // the target before the broadcast goes out. The receive path
      // would otherwise have a window where a piggyback message from
      // the target arrives and is accepted before the issuer's own
      // keyring has been mutated.
      applyRevocation(record, keyring);
      storeRevocation(record, bytes);
      emitMeshDiagnostic({
        kind: "revoke:issued",
        revokedPeerId: targetPeerId,
        issuerId: localPeerId,
      });
      const targets = [...connectedPeerIds];
      if (targets.length > 0) {
        networkAdapter.sendControlMessage(MESH_CONTROL_TYPE.Revocation, bytes, targets);
      }
    },
    get selfRevocation(): RevocationRecord | undefined {
      return selfRevocation;
    },
    close: async () => {
      signaling.close();
      webrtcAdapter?.disconnect();
      await repo.shutdown();
    },
  };
}

async function resolveKeyringSource(
  source: MeshKeyring | { storage: KeyringStorage } | { source: () => MeshKeyring }
): Promise<() => MeshKeyring> {
  if (typeof source === "object" && source !== null && "source" in source) {
    return source.source;
  }
  if ("storage" in source) {
    const loaded = await source.storage.load();
    if (loaded === null) {
      throw new Error(
        "createMeshClient: keyring storage returned null (no saved keyring). In a Node CLI, bootstrap with `bootstrapCliKeyring` from `@fairfox/polly/mesh/node`; in a browser, run your pairing flow first and save the keyring through the storage adapter before constructing the client."
      );
    }
    return () => loaded;
  }
  return () => source;
}
