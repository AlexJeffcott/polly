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
import { DEFAULT_MESH_KEY_ID, type MeshKeyring, MeshNetworkAdapter } from "./mesh-network-adapter";
import { MeshSignalingClient, type MeshSignalingClientOptions } from "./mesh-signaling-client";
import { configureMeshState } from "./mesh-state";
import { MeshWebRTCAdapter, type MeshWebRTCAdapterOptions } from "./mesh-webrtc-adapter";

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
    | undefined
): MeshClientHandleSnapshot {
  return {
    state,
    announcedToPeer: wire?.lastSyncMessageOutAt !== undefined,
    lastSyncMessageOutAt: wire?.lastSyncMessageOutAt,
    lastSyncMessageInAt: wire?.lastSyncMessageInAt,
    lastSyncMessageOutSize: wire?.lastSyncMessageOutSize,
    lastSyncMessageOutType: wire?.lastSyncMessageOutType,
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
  repoHandles: Record<string, { state: unknown } | undefined>
): MeshClientPeerStateSnapshot["peers"][number] {
  if (!peer.slot) {
    return { ...peer, slot: undefined } as MeshClientPeerStateSnapshot["peers"][number];
  }
  const enriched: Record<string, MeshClientHandleSnapshot> = {};
  for (const docId of knownHandleIds) {
    enriched[docId] = buildHandleEntry(
      stringifyHandleState(repoHandles[docId]),
      peer.slot.handles[docId]
    );
  }
  for (const docId of Object.keys(peer.slot.handles)) {
    if (enriched[docId]) continue;
    enriched[docId] = buildHandleEntry("unknown", peer.slot.handles[docId]);
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

  const networkAdapter = new MeshNetworkAdapter({
    base: webrtcAdapter,
    keyringSource,
    encryptionEnabled,
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
      const enrichedPeers: MeshClientPeerStateSnapshot["peers"] = base.peers.map((peer) =>
        enrichPeerSlot(peer, knownHandleIds, repoHandles)
      );
      const out: MeshClientPeerStateSnapshot = {
        localPeerId: base.localPeerId,
        knownPeerIds: base.knownPeerIds,
        presentPeerIds: base.presentPeerIds,
        sweep: base.sweep,
        peers: enrichedPeers,
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
