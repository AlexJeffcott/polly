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
    dataChannelLabel?: string;
  };
  /** The local peer's keyring — either a fully-constructed instance, or a
   * persistence adapter to load one from. When a storage adapter is given
   * and `storage.load()` resolves to `null`, the factory throws with a
   * message pointing at the bootstrap helper in `@fairfox/polly/mesh/node`;
   * we deliberately do not generate an identity silently. */
  keyring: MeshKeyring | { storage: KeyringStorage };
  /** Optional Automerge-Repo storage adapter. Applications that want
   * durable local state pass an IndexedDB adapter in browsers or a
   * filesystem adapter in Node; omitting it keeps the Repo in-memory. */
  repoStorage?: StorageAdapterInterface;
  /** When `false`, signs but does not encrypt. Defaults to `true` — the
   * full $meshState posture where the server is off the data path. */
  encryptionEnabled?: boolean;
}

/** Handle returned by {@link createMeshClient}. */
export interface MeshClient {
  /** The Automerge Repo. `$meshState` has already been configured against
   * this repo, so primitives just work — but the repo is exposed in case
   * the application needs it directly (server-side cron, bulk exports,
   * migration tools). */
  repo: Repo;
  /** The configured keyring. Exposed so the application can inspect or
   * mutate it (add authorised peers, apply revocations) and then
   * re-persist via its storage. */
  keyring: MeshKeyring;
  /** The signalling client. Exposed for applications that need to hook
   * lifecycle events or send custom signalling payloads. */
  signaling: MeshSignalingClient;
  /** The WebRTC network adapter. Exposed for advanced use (blob store
   * wiring, peer-connection introspection). */
  networkAdapter: MeshNetworkAdapter;
  /** The underlying WebRTC adapter wrapped by {@link networkAdapter}. */
  webrtcAdapter: MeshWebRTCAdapter;
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
  const keyring = await resolveKeyring(options.keyring);
  const encryptionEnabled = options.encryptionEnabled ?? true;

  // A mesh keyring must carry the per-Repo document key used by
  // MeshNetworkAdapter's encryption layer. We fail loud rather than
  // silently disable encryption when encryptionEnabled is true.
  if (encryptionEnabled && !keyring.documentKeys.has(DEFAULT_MESH_KEY_ID)) {
    throw new Error(
      `createMeshClient: encryption is enabled but the keyring has no document key for "${DEFAULT_MESH_KEY_ID}". Bootstrap or apply a pairing token that carries the document key before connecting.`
    );
  }

  const knownPeerIds = [...keyring.knownPeers.keys()].filter(
    (id) => id !== options.signaling.peerId
  );

  const webrtcAdapterOptions: MeshWebRTCAdapterOptions = {
    signaling: undefined as unknown as MeshSignalingClient, // wired after signaling construction
    peerId: options.signaling.peerId,
    knownPeerIds,
    ...(options.rtc?.iceServers !== undefined && { iceServers: options.rtc.iceServers }),
    ...(options.rtc?.dataChannelLabel !== undefined && {
      dataChannelLabel: options.rtc.dataChannelLabel,
    }),
    ...(options.rtc?.RTCPeerConnection !== undefined && {
      RTCPeerConnection: options.rtc.RTCPeerConnection,
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
    keyring,
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
    keyring,
    signaling,
    networkAdapter,
    webrtcAdapter,
    close: async () => {
      signaling.close();
      webrtcAdapter?.disconnect();
      await repo.shutdown();
    },
  };
}

async function resolveKeyring(
  source: MeshKeyring | { storage: KeyringStorage }
): Promise<MeshKeyring> {
  if ("storage" in source) {
    const loaded = await source.storage.load();
    if (loaded === null) {
      throw new Error(
        "createMeshClient: keyring storage returned null (no saved keyring). In a Node CLI, bootstrap with `bootstrapCliKeyring` from `@fairfox/polly/mesh/node`; in a browser, run your pairing flow first and save the keyring through the storage adapter before constructing the client."
      );
    }
    return loaded;
  }
  return source;
}
