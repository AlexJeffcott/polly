/**
 * mesh-webrtc-adapter — Phase 2 browser-side WebRTC transport for Polly's
 * $meshState primitive. Extends Automerge's NetworkAdapter base class and
 * uses real native RTCPeerConnection / RTCDataChannel instances to carry
 * sync messages between peers.
 *
 * This is the "base" transport that MeshNetworkAdapter wraps with its
 * sign-then-encrypt envelope. The stack is:
 *
 *   $meshState
 *     └─ Repo
 *          └─ MeshNetworkAdapter (sign + encrypt)
 *                └─ MeshWebRTCAdapter (real data channels)
 *                      └─ MeshSignalingClient (SDP/ICE relay)
 *                            └─ signalingServer (Elysia plugin on the host app)
 *
 * Because WebRTC lives in browsers, this module is browser-only. It
 * assumes global RTCPeerConnection, RTCDataChannel, and WebSocket types
 * are available. Under bun:test the classes cannot be exercised
 * end-to-end — the first validation path is either Playwright running a
 * real browser, a Puppeteer harness, or a human testing a browser-side
 * example app that consumes the adapter.
 *
 * What this module does at runtime:
 *
 * - Constructs a MeshWebRTCAdapter with a signalling client and a local
 *   peer id. No data channels exist at construction time.
 *
 * - When Automerge's NetworkSubsystem calls connect(peerId) on the
 *   adapter, it starts listening for signals from remote peers and is
 *   ready to build peer connections as they are discovered.
 *
 * - When a remote peer sends an SDP offer via the signalling channel,
 *   the adapter builds a fresh RTCPeerConnection, accepts the offer,
 *   produces an answer, sends it back through signalling, and wires the
 *   received data channel to emit Automerge Message events upward.
 *
 * - When the local repo calls send(message), the adapter looks up the
 *   peer connection for message.targetId and writes the serialised
 *   bytes to its data channel. If no connection exists yet, the adapter
 *   creates one by sending an SDP offer through signalling. Outgoing
 *   messages are queued until the channel is open.
 *
 * - Disconnect tears down every peer connection and closes the
 *   signalling client.
 */

import {
  type Message,
  NetworkAdapter,
  type PeerId,
  type PeerMetadata,
} from "@automerge/automerge-repo/slim";
import { isBlobMessageType } from "./blob-transfer";
import type { MeshKeyring } from "./mesh-network-adapter";
import type { MeshSignalingClient } from "./mesh-signaling-client";
import {
  chunkSyncMessage,
  isSyncFragmentType,
  parseSyncFragment,
  reassembleSyncFragments,
  SYNC_FRAGMENT_THRESHOLD,
} from "./sync-fragment";

/** Standard STUN servers for NAT traversal. In production, callers who
 * need TURN fallback for peers behind symmetric NATs should replace this
 * with their own ICE server list. */
export const DEFAULT_ICE_SERVERS: RTCIceServer[] = [
  { urls: "stun:stun.l.google.com:19302" },
  { urls: "stun:stun1.l.google.com:19302" },
];

/** Options for constructing a {@link MeshWebRTCAdapter}. */
export interface MeshWebRTCAdapterOptions {
  /** The signalling client the adapter uses to exchange SDP and ICE
   * candidates with other peers. Typically constructed once per
   * application and shared across any adapters that need it. */
  signaling: MeshSignalingClient;
  /** The local peer id. Must match the peer id the signalling client
   * registered with. */
  peerId: string;
  /** Peer ids to connect to on startup. When `connect()` is called, the
   * adapter iterates this list and initiates a WebRTC connection to each
   * one by sending an SDP offer through the signalling channel. Peers
   * not in this list can still connect by sending an offer *to* this
   * adapter. The natural source for this list is the keyring's
   * knownPeers map keys.
   *
   * Used only when {@link keyringSource} is not supplied. With
   * `keyringSource` set the adapter reads `knownPeers` live from the
   * keyring on every initiation decision, which is the shape
   * {@link createMeshClient} wires up so post-construction
   * {@link applyPairingToken} calls take effect without the consumer
   * having to call {@link MeshWebRTCAdapter.addKnownPeer} by hand. */
  knownPeerIds?: string[];
  /** Live keyring source. When supplied, the adapter reads
   * `knownPeers` from `keyringSource()` on every initiation decision
   * instead of a Set captured at construction. Combined with the
   * periodic re-sweep started in {@link MeshWebRTCAdapter.connect},
   * this makes mutations to `keyring.knownPeers` — including the ones
   * produced by {@link applyPairingToken} after the mesh client is up
   * — visible to the dial path within at most one sweep interval. The
   * crypto layer already re-reads the keyring on every send and
   * receive; this option closes the same loop for the WebRTC adapter.
   *
   * Polly issue #103: without this, a long-lived daemon that pairs a
   * new device after its mesh client is constructed never dials the
   * new peer — the adapter's captured Set stays stale even though the
   * keyring contains the new entry, and the lex-tie-break rule in
   * {@link MeshWebRTCAdapter.shouldInitiateTo} can leave both peers
   * waiting for the other to offer indefinitely. */
  keyringSource?: () => MeshKeyring;
  /** How often the adapter re-evaluates whether to dial peers in the
   * signalling roster. The sweep is what catches peers that became
   * authorised in the keyring after their `peer-joined` notification
   * already fired — the adapter has no other event to hang the retry
   * on, so it polls. Cheap: one Map lookup per present peer, fired at
   * most once per interval. Defaults to 2000ms; tests override to
   * shorten the failure budget. Set to 0 to disable the sweep
   * (the captured-set behaviour, kept only for migration). */
  knownPeersRefreshIntervalMs?: number;
  /** Optional ICE server list override. Defaults to {@link DEFAULT_ICE_SERVERS}. */
  iceServers?: RTCIceServer[];
  /** Optional data channel label. Defaults to "polly-mesh". Applications
   * that share a signalling server between multiple meshes may want
   * distinct labels per mesh. */
  dataChannelLabel?: string;
  /** RTCPeerConnection constructor. Defaults to
   * `globalThis.RTCPeerConnection`. Inject a different implementation
   * (e.g. `werift` or `@roamhq/wrtc`) when running outside a browser, or
   * to use a custom subclass for tests or instrumentation. */
  RTCPeerConnection?: typeof RTCPeerConnection;
}

/** Types of signalling payload this adapter exchanges through the
 * signalling channel. The signalling server treats these as opaque. */
type SignalingPayload =
  | { kind: "offer"; sdp: RTCSessionDescriptionInit }
  | { kind: "answer"; sdp: RTCSessionDescriptionInit }
  | { kind: "ice"; candidate: RTCIceCandidateInit };

/** State tracked for each remote peer. */
interface PeerSlot {
  connection: RTCPeerConnection;
  channel: RTCDataChannel | undefined;
  /** Outgoing messages queued while the channel is still connecting.
   * Typed as ArrayBuffer-backed so they are directly usable by
   * RTCDataChannel.send under TypeScript's strict buffer-source typing. */
  pendingSends: Uint8Array<ArrayBuffer>[];
  /** Partially-assembled inbound sync messages, keyed by the fragment id
   * stamped on each chunk. Entries are deleted as soon as the last
   * fragment for an id arrives and the reassembled bytes are dispatched. */
  pendingFragments: Map<string, { chunks: Map<number, Uint8Array>; total: number }>;
  /** Remote ICE candidates that arrived before `setRemoteDescription`
   * completed. addIceCandidate throws when `remoteDescription` is null,
   * and real Chrome 148+ does not internally queue these the way Chrome
   * for Testing does — so any candidate that wins the race against the
   * answer SDP would be silently dropped, leaving ICE checking with no
   * remote candidates to pair against. Drained from {@link handleAnswer}
   * and the post-`setRemoteDescription` step of {@link handleOffer}. */
  pendingRemoteIce: RTCIceCandidateInit[];
}

/**
 * Automerge-Repo NetworkAdapter backed by real WebRTC data channels.
 * Manages one RTCPeerConnection per remote peer and uses a supplied
 * {@link MeshSignalingClient} for SDP/ICE exchange.
 */
export class MeshWebRTCAdapter extends NetworkAdapter {
  readonly signaling: MeshSignalingClient;
  readonly iceServers: RTCIceServer[];
  readonly dataChannelLabel: string;
  /** Peers this adapter is willing to dial. Mutable so callers that pair
   * a new device after construction (e.g. a CLI `add-device` process whose
   * mesh client is long-lived across the pair ceremony) can register the
   * new peer with {@link addKnownPeer} without restarting the client.
   *
   * Used only in the captured-set fallback path — when no
   * {@link keyringSource} is supplied. With `keyringSource` set, the
   * authoritative source is the live keyring and this Set is unused. */
  private readonly knownPeers: Set<string>;
  /** Live keyring source, or undefined when the adapter is operating in
   * the captured-set fallback shape. See the JSDoc on
   * {@link MeshWebRTCAdapterOptions.keyringSource}. */
  private readonly keyringSource: (() => MeshKeyring) | undefined;
  /** Interval handle for the periodic re-sweep that catches peers
   * already in the signalling roster when the keyring grew. Cleared in
   * {@link MeshWebRTCAdapter.disconnect}. */
  private knownPeersRefreshTimer: ReturnType<typeof setInterval> | undefined;
  /** Sweep interval. Resolved from
   * {@link MeshWebRTCAdapterOptions.knownPeersRefreshIntervalMs} at
   * construction. Defaults to 2000ms; tests override to 100–250ms. */
  private readonly knownPeersRefreshIntervalMs: number;
  /** Peers currently visible in the signalling roster — populated by
   * {@link handlePeersPresent} / {@link handlePeerJoined} and pruned by
   * {@link handlePeerLeft}. Read by {@link addKnownPeer} to decide
   * whether the new peer is already online and an offer can fire now. */
  private readonly presentPeers = new Set<string>();
  /** Local peer id captured at construction time. The base
   * `NetworkAdapter.peerId` is only populated when `connect()` fires,
   * which means glare-resolution and peer-discovery dispatch would
   * otherwise have no id to compare against before the first incoming
   * message. Keeping a private mirror keeps those code paths honest
   * without depending on Automerge's lifecycle. */
  private readonly localPeerId: string;
  private readonly RTCPeerConnectionCtor: typeof RTCPeerConnection;
  private readonly slots = new Map<string, PeerSlot>();
  private ready = false;
  private readyResolver: (() => void) | undefined;

  /** The peers this adapter will dial. Backward-compatible read accessor
   * for callers that previously iterated the `knownPeerIds` array. With
   * a {@link MeshWebRTCAdapterOptions.keyringSource} configured, the
   * value is read live from the keyring; otherwise it falls back to the
   * captured Set populated through the constructor and
   * {@link addKnownPeer}. */
  get knownPeerIds(): string[] {
    if (this.keyringSource !== undefined) {
      return [...this.keyringSource().knownPeers.keys()].filter((id) => id !== this.localPeerId);
    }
    return [...this.knownPeers];
  }

  /** True iff `remotePeerId` is currently in the authoritative
   * knownPeers source — the live keyring when one was supplied, or
   * the captured Set otherwise. Centralises the membership check so
   * {@link shouldInitiateTo} and the JSDoc on
   * {@link MeshWebRTCAdapterOptions.keyringSource} agree on the rule. */
  private hasKnownPeer(remotePeerId: string): boolean {
    if (this.keyringSource !== undefined) {
      return this.keyringSource().knownPeers.has(remotePeerId);
    }
    return this.knownPeers.has(remotePeerId);
  }

  /** Callback for incoming blob messages. Set by the blob store.
   *  Called with the sender's peer ID, the raw header object, and the
   *  binary payload (chunk data). */
  onBlobMessage?: (peerId: string, header: Record<string, unknown>, data: Uint8Array) => void;

  constructor(options: MeshWebRTCAdapterOptions) {
    super();
    this.signaling = options.signaling;
    this.iceServers = options.iceServers ?? DEFAULT_ICE_SERVERS;
    this.dataChannelLabel = options.dataChannelLabel ?? "polly-mesh";
    this.knownPeers = new Set(options.knownPeerIds ?? []);
    this.keyringSource = options.keyringSource;
    this.knownPeersRefreshIntervalMs = options.knownPeersRefreshIntervalMs ?? 2000;
    this.localPeerId = options.peerId;
    const PC = options.RTCPeerConnection ?? globalThis.RTCPeerConnection;
    if (typeof PC !== "function") {
      throw new Error(
        "MeshWebRTCAdapter: no RTCPeerConnection implementation found. Pass one via options.RTCPeerConnection (e.g. from `werift` or `@roamhq/wrtc`), or run in a browser where `globalThis.RTCPeerConnection` exists."
      );
    }
    this.RTCPeerConnectionCtor = PC;
  }

  isReady(): boolean {
    return this.ready;
  }

  /** The current number of peer slots the adapter is tracking. Each
   * slot is one ordered pair (local peer ↔ remote peer) with its own
   * RTCPeerConnection and data channel. Exposed for tests that assert
   * "exactly one channel per pair" after discovery settles. */
  peerSlotCount(): number {
    return this.slots.size;
  }

  /** Snapshot of the adapter's per-peer state at the moment of the
   * call. Returned values are plain data — strings and booleans only —
   * so consumers can log, assert on, or render them without retaining
   * references into the adapter's internals.
   *
   * Polly issue #103 asked for an inspection surface so a consumer
   * harness can answer "is the mesh layer in a known good state" from
   * outside polly. This method is that surface. The fields mirror the
   * three layers of the WebRTC connection lifecycle so a "stuck"
   * connection can be diagnosed without reaching for the browser
   * devtools: the SDP signalling state, the ICE checking state, and
   * the unified RTCPeerConnection connection state. A `dataChannel`
   * field reports whether the data channel — the thing the mesh
   * actually carries bytes over — is open.
   *
   * Peers visible in the signalling roster but not yet dialled appear
   * with `slot: undefined`, so a consumer can tell "we know about this
   * peer in signalling but the WebRTC adapter has not started an
   * offer yet" from "we have a slot in some negotiation state". */
  getPeerStateSnapshot(): {
    localPeerId: string;
    knownPeerIds: string[];
    presentPeerIds: string[];
    peers: Array<{
      peerId: string;
      knownInKeyring: boolean;
      presentInSignalling: boolean;
      slot:
        | undefined
        | {
            signalingState: string;
            iceConnectionState: string;
            connectionState: string;
            dataChannelState: string;
            pendingSendCount: number;
            pendingRemoteIceCount: number;
          };
    }>;
  } {
    const knownPeerIds = this.knownPeerIds;
    const presentPeerIds = [...this.presentPeers];
    const knownPeerSet = new Set(knownPeerIds);
    const allPeers = new Set<string>();
    for (const id of knownPeerIds) allPeers.add(id);
    for (const id of presentPeerIds) allPeers.add(id);
    for (const id of this.slots.keys()) allPeers.add(id);
    const peers: ReturnType<MeshWebRTCAdapter["getPeerStateSnapshot"]>["peers"] = [];
    for (const peerId of allPeers) {
      const slot = this.slots.get(peerId);
      peers.push({
        peerId,
        knownInKeyring: knownPeerSet.has(peerId),
        presentInSignalling: this.presentPeers.has(peerId),
        slot: slot
          ? {
              signalingState: slot.connection.signalingState,
              iceConnectionState: slot.connection.iceConnectionState,
              connectionState: slot.connection.connectionState,
              dataChannelState: slot.channel?.readyState ?? "no-channel",
              pendingSendCount: slot.pendingSends.length,
              pendingRemoteIceCount: slot.pendingRemoteIce.length,
            }
          : undefined,
      });
    }
    return {
      localPeerId: this.localPeerId,
      knownPeerIds,
      presentPeerIds,
      peers,
    };
  }

  /** Handle the signalling server's `peer-joined` notification: a new
   * peer has appeared on the relay. If the peer is in `knownPeerIds`
   * and we do not already have a slot for it, and the tie-break rule
   * designates us as the initiator (our peerId compares greater than
   * theirs), open an initiating slot and fire the SDP offer. Otherwise
   * do nothing — either we are not interested in this peer, we are
   * already connected, or the other side is the one expected to
   * initiate. */
  handlePeerJoined(remotePeerId: string): void {
    this.presentPeers.add(remotePeerId);
    if (!this.shouldInitiateTo(remotePeerId)) return;
    this.createInitiatingSlot(remotePeerId);
  }

  /** Handle the signalling server's `peers-present` notification sent
   * once to a newcomer. Applies the same filter as handlePeerJoined to
   * every listed peer, so a device joining into an established lobby
   * dials every knownPeer it is meant to initiate to in one pass. */
  handlePeersPresent(peerIds: string[]): void {
    for (const remotePeerId of peerIds) {
      this.presentPeers.add(remotePeerId);
      if (!this.shouldInitiateTo(remotePeerId)) continue;
      this.createInitiatingSlot(remotePeerId);
    }
  }

  /** Handle the signalling server's `peer-left` notification: a
   * previously joined peer has closed its socket. Evict any slot we
   * hold for that peer so a subsequent `peer-joined` from the same
   * peerId (a reconnect) creates a fresh slot rather than colliding
   * with a stale RTCPeerConnection that WebRTC's own ICE timer has
   * not yet noticed is dead. */
  handlePeerLeft(remotePeerId: string): void {
    this.presentPeers.delete(remotePeerId);
    const slot = this.slots.get(remotePeerId);
    if (!slot) return;
    slot.channel?.close();
    slot.connection.close();
    this.slots.delete(remotePeerId);
  }

  /** Register a peer the adapter should dial. Used by post-construction
   * pair-acceptance flows — when a long-lived mesh client (e.g. a CLI
   * `add-device` process or a daemon holding the mesh open) accepts a
   * pair token after start-up, its keyring's `knownPeers` map gains a
   * new entry. Calling this method propagates that into the adapter's
   * own allowlist; if the peer is already in the signalling roster and
   * the tie-break rule names us as the initiator, an SDP offer fires
   * immediately. No-op if the peer is already known.
   *
   * When a {@link MeshWebRTCAdapterOptions.keyringSource} is configured
   * the adapter already reads `knownPeers` live and the periodic sweep
   * picks up the new entry within
   * {@link MeshWebRTCAdapterOptions.knownPeersRefreshIntervalMs} on its
   * own, so explicit calls to this method are not required for
   * correctness — but remain supported for callers that want the
   * "dial now if present" prompt without waiting for the next sweep. */
  addKnownPeer(remotePeerId: string): void {
    if (remotePeerId === this.localPeerId) return;
    if (this.keyringSource === undefined) {
      // Captured-set fallback path: keep the legacy mutation behaviour
      // so existing consumers that wire the adapter directly without a
      // keyringSource still work.
      if (this.knownPeers.has(remotePeerId)) return;
      this.knownPeers.add(remotePeerId);
    }
    if (!this.presentPeers.has(remotePeerId)) return;
    if (!this.shouldInitiateTo(remotePeerId)) return;
    this.createInitiatingSlot(remotePeerId);
  }

  /** Re-evaluate every peer currently in the signalling roster and
   * dial the ones the keyring authorises that we do not already have
   * a slot for. The periodic sweep started in {@link connect} calls
   * this; consumers can call it manually to skip the wait after they
   * apply a fresh pairing token. Idempotent. */
  refreshKnownPeers(): void {
    for (const remotePeerId of this.presentPeers) {
      if (!this.shouldInitiateTo(remotePeerId)) continue;
      this.createInitiatingSlot(remotePeerId);
    }
  }

  private shouldInitiateTo(remotePeerId: string): boolean {
    if (remotePeerId === this.localPeerId) return false;
    if (!this.hasKnownPeer(remotePeerId)) return false;
    if (this.slots.has(remotePeerId)) return false;
    // Tie-break: the lexicographically higher peer id initiates. This
    // matches the glare-resolution rule in handleOffer, so pre-offer
    // filtering eliminates the glare pathway for the common case where
    // both sides learn of each other at roughly the same moment.
    if (this.localPeerId <= remotePeerId) return false;
    return true;
  }

  whenReady(): Promise<void> {
    if (this.ready) return Promise.resolve();
    return new Promise((resolve) => {
      this.readyResolver = resolve;
    });
  }

  /**
   * Start the adapter. Marks the adapter ready so Automerge's
   * NetworkSubsystem begins routing messages through it. Discovery of
   * peers is driven entirely by the signalling server's
   * `peers-present` and `peer-joined` frames, handed to
   * {@link handlePeersPresent} and {@link handlePeerJoined}. A peer
   * that calls `signaling.connect()` at any point — before or after
   * this method — will either find its targets already in the server's
   * lobby (peers-present) or learn about them as they arrive
   * (peer-joined); either way the adapter only opens one
   * initiating slot per ordered pair.
   */
  connect(peerId: PeerId, peerMetadata?: PeerMetadata): void {
    this.peerId = peerId;
    if (peerMetadata !== undefined) {
      this.peerMetadata = peerMetadata;
    }
    this.ready = true;
    this.readyResolver?.();
    this.startKnownPeersSweep();
  }

  disconnect(): void {
    this.stopKnownPeersSweep();
    for (const slot of this.slots.values()) {
      slot.channel?.close();
      slot.connection.close();
    }
    this.slots.clear();
    this.signaling.close();
    this.ready = false;
    this.emit("close");
  }

  /** Start the periodic re-sweep that catches peers added to the
   * keyring after their `peer-joined` notification has already fired.
   * No-op when no keyringSource was supplied — the captured-set
   * fallback has no live source to re-read, so the sweep would be
   * useless. No-op when the interval is configured to 0. */
  private startKnownPeersSweep(): void {
    if (this.keyringSource === undefined) return;
    if (this.knownPeersRefreshIntervalMs <= 0) return;
    if (this.knownPeersRefreshTimer !== undefined) return;
    this.knownPeersRefreshTimer = setInterval(() => {
      this.refreshKnownPeers();
    }, this.knownPeersRefreshIntervalMs);
  }

  private stopKnownPeersSweep(): void {
    if (this.knownPeersRefreshTimer === undefined) return;
    clearInterval(this.knownPeersRefreshTimer);
    this.knownPeersRefreshTimer = undefined;
  }

  /**
   * Send a sync message to a specific remote peer. If no RTCPeerConnection
   * exists yet, the adapter initiates one by producing an SDP offer and
   * sending it through the signalling channel; the outgoing bytes are
   * queued until the data channel is open.
   */
  send(message: Message): void {
    const targetId = message.targetId as unknown as string;
    const bytes = this.serialiseMessage(message);
    let slot = this.slots.get(targetId);
    if (!slot) {
      slot = this.createInitiatingSlot(targetId);
    }
    if (slot.channel && slot.channel.readyState === "open") {
      this.sendBytesMaybeFragmented(slot.channel, bytes);
    } else {
      slot.pendingSends.push(bytes);
    }
  }

  /** Send raw wire bytes, fragmenting if they exceed the SCTP maxMessageSize
   *  cap. The default RTCDataChannel limit is 256 KiB in current Chrome and
   *  werift; oversized sends either throw, drop silently, or stall the
   *  channel, none of which surface as an error to the caller. Fragments
   *  use the same length-prefixed JSON header wire format as ordinary
   *  messages but carry a `sync-fragment` type that the receive path
   *  detects and reassembles before deserialising. */
  private sendBytesMaybeFragmented(channel: RTCDataChannel, bytes: Uint8Array<ArrayBuffer>): void {
    if (bytes.length <= SYNC_FRAGMENT_THRESHOLD) {
      channel.send(bytes);
      return;
    }
    const id = crypto.randomUUID();
    const fragments = chunkSyncMessage(bytes, id);
    for (const fragment of fragments) {
      channel.send(fragment);
    }
  }

  /**
   * Entry point the signalling client calls when it receives a signal
   * from a remote peer. Dispatches on the payload `kind` to either
   * accept an offer (building an answer), apply an answer, or add an
   * ICE candidate. Exposed publicly so the caller that constructs the
   * signalling client can wire the onSignal callback directly to this
   * method.
   */
  handleSignal(fromPeerId: string, rawPayload: unknown): void {
    const payload = rawPayload as unknown as SignalingPayload;
    if (!payload || typeof payload !== "object" || !("kind" in payload)) {
      return;
    }
    switch (payload.kind) {
      case "offer":
        void this.handleOffer(fromPeerId, payload.sdp);
        return;
      case "answer":
        void this.handleAnswer(fromPeerId, payload.sdp);
        return;
      case "ice":
        void this.handleIceCandidate(fromPeerId, payload.candidate);
        return;
    }
  }

  private createInitiatingSlot(targetId: string): PeerSlot {
    const connection = new this.RTCPeerConnectionCtor({ iceServers: this.iceServers });
    const channel = connection.createDataChannel(this.dataChannelLabel, { ordered: true });
    const slot: PeerSlot = {
      connection,
      channel,
      pendingSends: [],
      pendingFragments: new Map(),
      pendingRemoteIce: [],
    };
    this.slots.set(targetId, slot);
    this.wireConnection(targetId, connection);
    this.wireDataChannel(targetId, channel);
    void this.initiateOffer(targetId, connection);
    return slot;
  }

  private async initiateOffer(targetId: string, connection: RTCPeerConnection): Promise<void> {
    const offer = await connection.createOffer();
    await connection.setLocalDescription(offer);
    this.signaling.sendSignal(targetId, { kind: "offer", sdp: offer } satisfies SignalingPayload);
  }

  private async handleOffer(fromPeerId: string, sdp: RTCSessionDescriptionInit): Promise<void> {
    const existing = this.slots.get(fromPeerId);
    if (existing) {
      // Glare: we already initiated a connection to this peer. Resolve by
      // peer-id ordering: the lexicographically lower id yields its own
      // offer and accepts the incoming one. The higher id ignores the
      // incoming offer and waits for the answer to its own.
      const localId = this.peerId as unknown as string;
      if (localId > fromPeerId) {
        return;
      }
      existing.channel?.close();
      existing.connection.close();
      this.slots.delete(fromPeerId);
    }

    const connection = new this.RTCPeerConnectionCtor({ iceServers: this.iceServers });
    const slot: PeerSlot = {
      connection,
      channel: undefined,
      pendingSends: [],
      pendingFragments: new Map(),
      pendingRemoteIce: [],
    };
    this.slots.set(fromPeerId, slot);
    this.wireConnection(fromPeerId, connection);
    connection.ondatachannel = (event) => {
      slot.channel = event.channel;
      this.wireDataChannel(fromPeerId, event.channel);
    };
    await connection.setRemoteDescription(sdp);
    await this.flushPendingRemoteIce(slot);
    const answer = await connection.createAnswer();
    await connection.setLocalDescription(answer);
    this.signaling.sendSignal(fromPeerId, {
      kind: "answer",
      sdp: answer,
    } satisfies SignalingPayload);
  }

  private async handleAnswer(fromPeerId: string, sdp: RTCSessionDescriptionInit): Promise<void> {
    const slot = this.slots.get(fromPeerId);
    if (!slot) return;
    // Drop answers that arrive after the connection has already settled
    // — the signalling relay can echo a peer's frames more than once
    // under reconnect or reload, and a duplicate answer in the `stable`
    // state otherwise throws `InvalidStateError` and kills the slot. We
    // only ever expect an answer while we still have a local offer
    // pending; anything else is benign noise.
    if (slot.connection.signalingState !== "have-local-offer") return;
    await slot.connection.setRemoteDescription(sdp);
    await this.flushPendingRemoteIce(slot);
  }

  private async handleIceCandidate(
    fromPeerId: string,
    candidate: RTCIceCandidateInit
  ): Promise<void> {
    const slot = this.slots.get(fromPeerId);
    if (!slot) return;
    // If the answerer gathers ICE faster than its answer SDP travels
    // back through the signalling relay, candidates can land here before
    // `setRemoteDescription` has run. addIceCandidate throws when
    // `remoteDescription` is null on Chrome 148+, and the spec does not
    // require browsers to queue these internally — so buffer until the
    // remote description is set and drain in handleAnswer/handleOffer.
    if (slot.connection.remoteDescription === null) {
      slot.pendingRemoteIce.push(candidate);
      return;
    }
    try {
      await slot.connection.addIceCandidate(candidate);
    } catch {
      // Ignore candidate errors — a stale candidate after the connection
      // has already opened is benign.
    }
  }

  /** Drain the per-slot queue of remote ICE candidates that arrived
   * before `setRemoteDescription` completed. Errors per candidate are
   * swallowed for the same reason {@link handleIceCandidate} swallows
   * them — a single bad candidate must not stall the connection. */
  private async flushPendingRemoteIce(slot: PeerSlot): Promise<void> {
    if (slot.pendingRemoteIce.length === 0) return;
    const queued = slot.pendingRemoteIce;
    slot.pendingRemoteIce = [];
    for (const candidate of queued) {
      try {
        await slot.connection.addIceCandidate(candidate);
      } catch {
        // Same rationale as the live-path catch in handleIceCandidate.
      }
    }
  }

  private wireConnection(peerId: string, connection: RTCPeerConnection): void {
    connection.onicecandidate = (event) => {
      if (event.candidate) {
        this.signaling.sendSignal(peerId, {
          kind: "ice",
          candidate: event.candidate.toJSON(),
        } satisfies SignalingPayload);
      }
    };
    connection.onconnectionstatechange = () => {
      const state = connection.connectionState;
      if (state === "connected") {
        this.emit("peer-candidate", {
          peerId: peerId as unknown as PeerId,
          peerMetadata: {},
        });
      } else if (state === "disconnected" || state === "failed" || state === "closed") {
        this.slots.delete(peerId);
        this.emit("peer-disconnected", { peerId: peerId as unknown as PeerId });
      }
    };
  }

  private wireDataChannel(peerId: string, channel: RTCDataChannel): void {
    channel.onopen = () => {
      const slot = this.slots.get(peerId);
      if (!slot) return;
      // Drain any pending sends that were queued while the channel
      // was still connecting. The fragmenting helper handles oversized
      // payloads the same way it would on a live send.
      for (const bytes of slot.pendingSends) {
        this.sendBytesMaybeFragmented(channel, bytes);
      }
      slot.pendingSends = [];
    };
    channel.onmessage = (event) => {
      const data = event.data;
      if (data instanceof ArrayBuffer) {
        this.dispatchMessage(peerId, new Uint8Array(data));
      } else if (data instanceof Uint8Array) {
        this.dispatchMessage(peerId, data);
      }
      // Other types (strings, Blobs) are ignored — Polly's mesh transport
      // only sends binary payloads via this adapter.
    };
    channel.onclose = () => {
      const slot = this.slots.get(peerId);
      if (slot?.channel === channel) {
        slot.channel = undefined;
      }
    };
  }

  private dispatchMessage(fromPeerId: string, bytes: Uint8Array): void {
    try {
      // Intercept sync-fragments first: an oversized Automerge sync
      // message is split into fragments on the sender side because a
      // single RTCDataChannel.send above the SCTP maxMessageSize cap
      // silently drops or stalls the channel. Reassemble and re-dispatch
      // once every fragment of an id has arrived.
      if (isSyncFragmentType(bytes)) {
        this.handleSyncFragment(fromPeerId, bytes);
        return;
      }
      // Intercept blob messages before they reach the Automerge deserialiser.
      // Blob headers have type fields starting with "blob-" and would fail
      // MeshNetworkAdapter's signed-envelope unwrap if passed through.
      if (this.onBlobMessage && isBlobMessageType(bytes)) {
        const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        const headerLen = view.getUint32(0, false);
        const header = JSON.parse(
          new TextDecoder().decode(bytes.subarray(4, 4 + headerLen))
        ) as Record<string, unknown>;
        const data = bytes.subarray(4 + headerLen);
        this.onBlobMessage(fromPeerId, header, data);
        return;
      }
      const message = this.deserialiseMessage(bytes);
      this.emit("message", message);
    } catch {
      // Drop malformed messages silently — the MeshNetworkAdapter wrapper
      // also drops on verification failure, so a corrupt frame at this
      // layer is observationally the same as a forgery at the layer above.
    }
  }

  private handleSyncFragment(fromPeerId: string, bytes: Uint8Array): void {
    const parsed = parseSyncFragment(bytes);
    if (!parsed) return;
    const slot = this.slots.get(fromPeerId);
    if (!slot) return;
    const { header, data } = parsed;
    let entry = slot.pendingFragments.get(header.id);
    if (!entry) {
      entry = { chunks: new Map(), total: header.total };
      slot.pendingFragments.set(header.id, entry);
    }
    // The data view is a window onto the wire frame buffer. Copy out so
    // the reassembled message owns its bytes and the wire frame can be
    // garbage-collected.
    entry.chunks.set(header.index, data.slice());
    if (entry.chunks.size < entry.total) return;
    slot.pendingFragments.delete(header.id);
    const reassembled = reassembleSyncFragments(entry.chunks, entry.total);
    this.dispatchMessage(fromPeerId, reassembled);
  }

  /** Peer IDs with an open data channel, suitable for blob requests. */
  get connectedPeerIds(): string[] {
    const ids: string[] = [];
    for (const [peerId, slot] of this.slots) {
      if (slot.channel && slot.channel.readyState === "open") {
        ids.push(peerId);
      }
    }
    return ids;
  }

  /** Send a pre-serialised blob message to a specific peer. Returns false
   *  if the peer is not connected or the send buffer is above the high-water
   *  mark (caller should retry after a delay). */
  sendBlobMessage(peerId: string, bytes: Uint8Array<ArrayBuffer>): boolean {
    const slot = this.slots.get(peerId);
    if (!slot?.channel || slot.channel.readyState !== "open") return false;
    return this.trySendOnChannel(slot.channel, bytes);
  }

  /** Send bytes on a data channel if the buffer is below the high-water
   *  mark. Returns true if sent, false if backpressure applies. */
  private trySendOnChannel(channel: RTCDataChannel, bytes: Uint8Array<ArrayBuffer>): boolean {
    // 256 KiB high-water mark — matches the blob transfer default.
    if (channel.bufferedAmount > 256 * 1024) return false;
    channel.send(bytes);
    return true;
  }

  /** Pack an Automerge Message into binary for transmission over the
   * data channel. The format mirrors MeshNetworkAdapter's internal
   * serialisation: a length-prefixed JSON header followed by the raw
   * data bytes. Returns a Uint8Array<ArrayBuffer> so the result is
   * directly usable by RTCDataChannel.send under TypeScript's strict
   * buffer-source typing. */
  private serialiseMessage(message: Message): Uint8Array<ArrayBuffer> {
    const headerObj: Record<string, unknown> = {
      type: message.type,
      senderId: message.senderId,
      targetId: message.targetId,
    };
    if ("documentId" in message && message.documentId !== undefined) {
      headerObj["documentId"] = message.documentId;
    }
    const headerBytes = new TextEncoder().encode(JSON.stringify(headerObj));
    const dataBytes: Uint8Array =
      "data" in message && message.data instanceof Uint8Array ? message.data : new Uint8Array(0);
    const size = 4 + headerBytes.length + dataBytes.length;
    const buffer = new ArrayBuffer(size);
    const out = new Uint8Array(buffer);
    const view = new DataView(buffer);
    view.setUint32(0, headerBytes.length, false);
    out.set(headerBytes, 4);
    out.set(dataBytes, 4 + headerBytes.length);
    return out;
  }

  /** Inverse of {@link serialiseMessage}. */
  private deserialiseMessage(bytes: Uint8Array): Message {
    if (bytes.length < 4) {
      throw new Error("MeshWebRTCAdapter: message too short to deserialise.");
    }
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const headerLen = view.getUint32(0, false);
    if (bytes.length < 4 + headerLen) {
      throw new Error("MeshWebRTCAdapter: message header truncated.");
    }
    const header = JSON.parse(new TextDecoder().decode(bytes.subarray(4, 4 + headerLen)));
    const data = bytes.slice(4 + headerLen);
    return { ...header, data } as unknown as Message;
  }
}
