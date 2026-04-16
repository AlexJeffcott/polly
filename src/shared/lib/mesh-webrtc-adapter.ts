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
} from "@automerge/automerge-repo";
import type { MeshSignalingClient } from "./mesh-signaling-client";

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
   * knownPeers map keys. */
  knownPeerIds?: string[];
  /** Optional ICE server list override. Defaults to {@link DEFAULT_ICE_SERVERS}. */
  iceServers?: RTCIceServer[];
  /** Optional data channel label. Defaults to "polly-mesh". Applications
   * that share a signalling server between multiple meshes may want
   * distinct labels per mesh. */
  dataChannelLabel?: string;
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
  readonly knownPeerIds: string[];
  private readonly slots = new Map<string, PeerSlot>();
  private ready = false;
  private readyResolver: (() => void) | undefined;

  constructor(options: MeshWebRTCAdapterOptions) {
    super();
    this.signaling = options.signaling;
    this.iceServers = options.iceServers ?? DEFAULT_ICE_SERVERS;
    this.dataChannelLabel = options.dataChannelLabel ?? "polly-mesh";
    this.knownPeerIds = options.knownPeerIds ?? [];
  }

  isReady(): boolean {
    return this.ready;
  }

  whenReady(): Promise<void> {
    if (this.ready) return Promise.resolve();
    return new Promise((resolve) => {
      this.readyResolver = resolve;
    });
  }

  /**
   * Start the adapter. Wires the signalling client's onSignal callback
   * to the adapter's dispatch, opens the signalling connection if it
   * is not already open, and marks the adapter ready.
   */
  connect(peerId: PeerId, peerMetadata?: PeerMetadata): void {
    this.peerId = peerId;
    if (peerMetadata !== undefined) {
      this.peerMetadata = peerMetadata;
    }
    this.ready = true;
    this.readyResolver?.();

    // Initiate WebRTC connections to every known peer. This is the
    // discovery step: once the SDP exchange completes and the data
    // channel opens, the adapter emits 'peer-candidate' and the Repo's
    // NetworkSubsystem learns about the peer.
    for (const remotePeerId of this.knownPeerIds) {
      if (remotePeerId !== (peerId as unknown as string) && !this.slots.has(remotePeerId)) {
        this.createInitiatingSlot(remotePeerId);
      }
    }
  }

  disconnect(): void {
    for (const slot of this.slots.values()) {
      slot.channel?.close();
      slot.connection.close();
    }
    this.slots.clear();
    this.signaling.close();
    this.ready = false;
    this.emit("close");
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
      slot.channel.send(bytes);
    } else {
      slot.pendingSends.push(bytes);
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
    const connection = new RTCPeerConnection({ iceServers: this.iceServers });
    const channel = connection.createDataChannel(this.dataChannelLabel, { ordered: true });
    const slot: PeerSlot = { connection, channel, pendingSends: [] };
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

    const connection = new RTCPeerConnection({ iceServers: this.iceServers });
    const slot: PeerSlot = { connection, channel: undefined, pendingSends: [] };
    this.slots.set(fromPeerId, slot);
    this.wireConnection(fromPeerId, connection);
    connection.ondatachannel = (event) => {
      slot.channel = event.channel;
      this.wireDataChannel(fromPeerId, event.channel);
    };
    await connection.setRemoteDescription(sdp);
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
    await slot.connection.setRemoteDescription(sdp);
  }

  private async handleIceCandidate(
    fromPeerId: string,
    candidate: RTCIceCandidateInit
  ): Promise<void> {
    const slot = this.slots.get(fromPeerId);
    if (!slot) return;
    try {
      await slot.connection.addIceCandidate(candidate);
    } catch {
      // Ignore candidate errors — a stale candidate after the connection
      // has already opened is benign.
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
      // was still connecting.
      for (const bytes of slot.pendingSends) {
        channel.send(bytes);
      }
      slot.pendingSends = [];
    };
    channel.onmessage = (event) => {
      const data = event.data;
      if (data instanceof ArrayBuffer) {
        this.dispatchMessage(new Uint8Array(data));
      } else if (data instanceof Uint8Array) {
        this.dispatchMessage(data);
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

  private dispatchMessage(bytes: Uint8Array): void {
    try {
      const message = this.deserialiseMessage(bytes);
      this.emit("message", message);
    } catch {
      // Drop malformed messages silently — the MeshNetworkAdapter wrapper
      // also drops on verification failure, so a corrupt frame at this
      // layer is observationally the same as a forgery at the layer above.
    }
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
