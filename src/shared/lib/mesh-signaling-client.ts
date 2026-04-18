/**
 * mesh-signaling-client — browser-side client for Polly's signalingServer
 * Elysia plugin. Connects to the signalling WebSocket, registers a peer
 * id, and relays SDP/ICE messages between local WebRTC connections and
 * remote peers.
 *
 * This module is the companion to {@link signalingServer} from the Elysia
 * plugin family. The server accepts "join" and "signal" messages; this
 * client produces them. The protocol matches: opening the connection,
 * sending a "join" with the local peer id, and then using sendSignal()
 * to forward SDP and ICE messages to specific target peers.
 *
 * Because this client is browser-only in its first incarnation — it
 * assumes the global `WebSocket` is available — it cannot be exercised
 * under bun:test the way the server-side plugin is. The first validation
 * of this code path is either a Playwright harness or a human running
 * the browser-side example that consumes it.
 */

/** A signal message either sent to or received from the signalling server.
 * Matches the wire format produced by the Elysia signalingServer plugin. */
export interface SignalingMessage {
  type: "join" | "signal" | "error" | "peers-present" | "peer-joined" | "peer-left";
  peerId?: string;
  peerIds?: string[];
  targetPeerId?: string;
  payload?: unknown;
  reason?: "unknown-target" | "not-joined" | "malformed";
}

/** Options for constructing a {@link MeshSignalingClient}. */
export interface MeshSignalingClientOptions {
  /** The signalling server URL (ws:// or wss://). */
  url: string;
  /** The local peer id that this client will register with on join. */
  peerId: string;
  /** Callback invoked whenever a signal message from another peer arrives.
   * The receiver dispatches to the right PeerConnection based on the
   * `fromPeerId`. */
  onSignal: (fromPeerId: string, payload: unknown) => void;
  /** Optional callback invoked when the server returns an error (for
   * diagnostic UI or reconnection logic). */
  onError?: (reason: string, targetPeerId?: string) => void;
  /** Optional callback for the open and close lifecycle events. */
  onOpen?: () => void;
  onClose?: () => void;
  /** Optional callback invoked once, immediately after the server's
   * response to our `join`, listing every peer already joined at that
   * moment. Empty list when the lobby is otherwise empty. */
  onPeersPresent?: (peerIds: string[]) => void;
  /** Optional callback invoked each time a new peer joins the signalling
   * server after we have already joined. */
  onPeerJoined?: (peerId: string) => void;
  /** Optional callback invoked each time a joined peer's socket closes
   * (including graceful disconnect and abrupt drops detected by the
   * server). Fires at most once per departure. */
  onPeerLeft?: (peerId: string) => void;
  /** WebSocket constructor. Defaults to `globalThis.WebSocket`. Inject a
   * different implementation (e.g. `ws` package's `WebSocket`) when running
   * in an environment without a native WebSocket global, or to use a custom
   * subclass for tests or instrumentation. */
  WebSocket?: typeof WebSocket;
}

/**
 * Thin wrapper around a WebSocket connection to a Polly signalling server.
 * Handles the join handshake, routes incoming signals to the supplied
 * callback, and exposes a {@link sendSignal} method for outgoing signals.
 *
 * This class is deliberately small. It has no opinion on the signal
 * payload shape (the wire carries it as `unknown`), so it can carry SDP
 * offers, SDP answers, ICE candidates, or any other message the
 * WebRTC adapter wants to exchange with peers.
 */
export class MeshSignalingClient {
  readonly url: string;
  readonly peerId: string;
  private readonly onSignal: (fromPeerId: string, payload: unknown) => void;
  private readonly onError?: (reason: string, targetPeerId?: string) => void;
  private readonly onOpen?: () => void;
  private readonly onClose?: () => void;
  private readonly onPeersPresent?: (peerIds: string[]) => void;
  private readonly onPeerJoined?: (peerId: string) => void;
  private readonly onPeerLeft?: (peerId: string) => void;
  private socket: WebSocket | undefined;
  private joined = false;
  private readonly WebSocketCtor: typeof WebSocket;

  constructor(options: MeshSignalingClientOptions) {
    this.url = options.url;
    this.peerId = options.peerId;
    this.onSignal = options.onSignal;
    if (options.onError !== undefined) this.onError = options.onError;
    if (options.onOpen !== undefined) this.onOpen = options.onOpen;
    if (options.onClose !== undefined) this.onClose = options.onClose;
    if (options.onPeersPresent !== undefined) this.onPeersPresent = options.onPeersPresent;
    if (options.onPeerJoined !== undefined) this.onPeerJoined = options.onPeerJoined;
    if (options.onPeerLeft !== undefined) this.onPeerLeft = options.onPeerLeft;
    const WS = options.WebSocket ?? globalThis.WebSocket;
    if (typeof WS !== "function") {
      throw new Error(
        "MeshSignalingClient: no WebSocket implementation found. Pass one via options.WebSocket, or run in an environment where `globalThis.WebSocket` exists (Node 21+, Bun, browsers)."
      );
    }
    this.WebSocketCtor = WS;
  }

  /**
   * Open the WebSocket and send the join message. Resolves once the
   * connection is open; callers should not send signals before this
   * promise resolves.
   */
  async connect(): Promise<void> {
    return new Promise((resolve, reject) => {
      const ws = new this.WebSocketCtor(this.url);
      this.socket = ws;

      ws.addEventListener("open", () => {
        // Send the join message as the first frame. The server registers
        // the peer id and uses it as the authenticated sender for all
        // subsequent signals on this connection.
        ws.send(JSON.stringify({ type: "join", peerId: this.peerId } satisfies SignalingMessage));
        this.joined = true;
        this.onOpen?.();
        resolve();
      });

      ws.addEventListener("message", (event) => {
        this.dispatchFrame(event.data);
      });

      ws.addEventListener("error", (err) => {
        reject(err);
      });

      ws.addEventListener("close", () => {
        this.joined = false;
        this.onClose?.();
      });
    });
  }

  /**
   * Parse and route an incoming frame. Extracted from the open/message
   * closure in {@link connect} so the discriminated-union switch stays
   * below the linter's cognitive-complexity ceiling.
   */
  private dispatchFrame(raw: unknown): void {
    let msg: SignalingMessage;
    try {
      msg = typeof raw === "string" ? JSON.parse(raw) : (raw as SignalingMessage);
    } catch {
      return;
    }
    switch (msg.type) {
      case "signal":
        if (typeof msg.peerId === "string") this.onSignal(msg.peerId, msg.payload);
        return;
      case "peers-present":
        if (Array.isArray(msg.peerIds)) this.onPeersPresent?.(msg.peerIds);
        return;
      case "peer-joined":
        if (typeof msg.peerId === "string") this.onPeerJoined?.(msg.peerId);
        return;
      case "peer-left":
        if (typeof msg.peerId === "string") this.onPeerLeft?.(msg.peerId);
        return;
      case "error":
        if (msg.reason) this.onError?.(msg.reason, msg.targetPeerId);
        return;
      default:
        return;
    }
  }

  /**
   * Send a signal to another peer via the signalling server. The server
   * validates the sender (replacing the claimed peerId with the
   * authenticated join id) and routes to the target. Returns true if
   * the message was sent, false if the connection is not open.
   */
  sendSignal(targetPeerId: string, payload: unknown): boolean {
    if (!this.socket || this.socket.readyState !== this.WebSocketCtor.OPEN || !this.joined) {
      return false;
    }
    const msg: SignalingMessage = {
      type: "signal",
      peerId: this.peerId,
      targetPeerId,
      payload,
    };
    this.socket.send(JSON.stringify(msg));
    return true;
  }

  /**
   * Close the underlying WebSocket connection. The server's close handler
   * will evict this peer from its routing table.
   */
  close(): void {
    this.socket?.close();
    this.socket = undefined;
    this.joined = false;
  }

  /** True if the signalling connection is open and joined. */
  get isConnected(): boolean {
    return this.joined && this.socket?.readyState === this.WebSocketCtor.OPEN;
  }
}
