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
   * connectionState / data-channel state, and queued-send / queued-ICE
   * depth. Plain data, safe to log or render. Exists so a consumer
   * harness can answer "is the mesh layer in a known good state"
   * without instrumenting polly internals. Polly issue #103 item 7. */
  getPeerStateSnapshot(): ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>;
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
          peers: [],
        };
      }
      return webrtcAdapter.getPeerStateSnapshot();
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
