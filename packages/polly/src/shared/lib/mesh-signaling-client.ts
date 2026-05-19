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

/** A frame whose `type` is outside the built-in {@link SignalingMessage}
 * vocabulary. Consumers who want to layer application protocols on the
 * signalling socket — pairing return tokens, presence pings, anything
 * else that benefits from sharing the existing connection and its
 * reconnect state — receive these through {@link MeshSignalingClientOptions.onCustomFrame}
 * and produce them through {@link MeshSignalingClient.sendCustom}. Polly
 * does not interpret the body; the signalling server routes it per its
 * own conventions. The field `type` is always present; everything else
 * is application-defined. */
export interface CustomSignalingFrame {
  type: string;
  [key: string]: unknown;
}

/** Options for constructing a {@link MeshSignalingClient}. */
export interface MeshSignalingClientOptions {
  /** The signalling server URL — unencrypted scheme for local dev, TLS-terminated for production. */
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
  /** Optional callback invoked for any frame whose `type` is outside the
   * built-in {@link SignalingMessage} vocabulary. Consumers use this to
   * layer their own protocol on top of the signalling socket — pairing
   * return tokens, presence pings, anything else that benefits from
   * sharing the existing connection and its reconnect state. A frame
   * that arrives before the join handshake completes or that fails to
   * parse as JSON is dropped silently, as with the built-in types. */
  onCustomFrame?: (frame: CustomSignalingFrame) => void;
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
/** Base delay (ms) between reconnect attempts. Doubles per attempt up
 * to {@link RECONNECT_MAX_DELAY_MS}. */
const RECONNECT_BASE_DELAY_MS = 250;
/** Ceiling for the exponential backoff so a long outage does not leave
 * the client silent for minutes between probes. */
const RECONNECT_MAX_DELAY_MS = 30_000;

/** Parse a raw frame from the socket into a record with a string `type`,
 * or `undefined` if the frame is unparseable or malformed. Extracted so
 * {@link MeshSignalingClient.dispatchFrame} stays below the linter's
 * cognitive-complexity ceiling. */
function parseFrame(raw: unknown): Record<string, unknown> | undefined {
  let parsed: unknown;
  try {
    parsed = typeof raw === "string" ? JSON.parse(raw) : raw;
  } catch {
    return undefined;
  }
  if (typeof parsed !== "object" || parsed === null) {
    return undefined;
  }
  const record = parsed as unknown as Record<string, unknown>;
  if (typeof record["type"] !== "string") {
    return undefined;
  }
  return record;
}

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
  private readonly onCustomFrame?: (frame: CustomSignalingFrame) => void;
  private socket: WebSocket | undefined;
  private joined = false;
  private stopping = false;
  private reconnectTimer: ReturnType<typeof setTimeout> | undefined;
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
    if (options.onCustomFrame !== undefined) this.onCustomFrame = options.onCustomFrame;
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
    this.stopping = false;
    if (this.reconnectTimer) {
      clearTimeout(this.reconnectTimer);
      this.reconnectTimer = undefined;
    }
    return new Promise((resolve, reject) => {
      const ws = new this.WebSocketCtor(this.url);
      this.socket = ws;
      let settled = false;

      ws.addEventListener("open", () => {
        // Send the join message as the first frame. The server registers
        // the peer id and uses it as the authenticated sender for all
        // subsequent signals on this connection.
        ws.send(JSON.stringify({ type: "join", peerId: this.peerId } satisfies SignalingMessage));
        this.joined = true;
        this.onOpen?.();
        if (!settled) {
          settled = true;
          resolve();
        }
      });

      ws.addEventListener("message", (event) => {
        this.dispatchFrame(event.data);
      });

      ws.addEventListener("error", (err) => {
        // Only the initial connect rejects here. Post-open errors route
        // through the close handler's reconnect path.
        if (!settled) {
          settled = true;
          reject(err);
        }
      });

      ws.addEventListener("close", () => {
        const wasOpen = this.joined;
        this.joined = false;
        this.onClose?.();
        // If the caller asked to stop, respect it. Otherwise a close on
        // an established connection — or a close that preempted `open`
        // — kicks off the reconnect loop.
        if (!this.stopping && wasOpen) {
          this.scheduleReconnect(0);
        }
      });
    });
  }

  /** Schedule the next reconnect attempt with exponential backoff. */
  private scheduleReconnect(attempt: number): void {
    if (this.stopping) return;
    const delay = Math.min(RECONNECT_MAX_DELAY_MS, RECONNECT_BASE_DELAY_MS * 2 ** attempt);
    this.reconnectTimer = setTimeout(() => {
      this.reconnectTimer = undefined;
      if (this.stopping) return;
      void this.connect().catch(() => {
        this.scheduleReconnect(attempt + 1);
      });
    }, delay);
  }

  /**
   * Parse and route an incoming frame. Extracted from the open/message
   * closure in {@link connect} so the discriminated-union switch stays
   * below the linter's cognitive-complexity ceiling.
   */
  private dispatchFrame(raw: unknown): void {
    const record = parseFrame(raw);
    if (record === undefined) {
      return;
    }
    const handler = this.builtInHandler(record["type"]);
    if (handler !== undefined) {
      handler(record);
      return;
    }
    // Unknown types route to the custom-frame handler, which consumers
    // use to layer application protocols on the shared socket. Without
    // a handler the frame is silently dropped, preserving the old
    // behaviour byte-for-byte.
    this.onCustomFrame?.(record as unknown as CustomSignalingFrame);
  }

  private builtInHandler(type: unknown): ((record: Record<string, unknown>) => void) | undefined {
    if (type === "signal") {
      return (record) => {
        if (typeof record["peerId"] === "string") {
          this.onSignal(record["peerId"], record["payload"]);
        }
      };
    }
    if (type === "peers-present") {
      return (record) => {
        if (Array.isArray(record["peerIds"])) {
          this.onPeersPresent?.(record["peerIds"] as unknown as string[]);
        }
      };
    }
    if (type === "peer-joined") {
      return (record) => {
        if (typeof record["peerId"] === "string") {
          this.onPeerJoined?.(record["peerId"]);
        }
      };
    }
    if (type === "peer-left") {
      return (record) => {
        if (typeof record["peerId"] === "string") {
          this.onPeerLeft?.(record["peerId"]);
        }
      };
    }
    if (type === "error") {
      return (record) => {
        if (typeof record["reason"] !== "string") {
          return;
        }
        const targetPeerId =
          typeof record["targetPeerId"] === "string" ? record["targetPeerId"] : undefined;
        this.onError?.(record["reason"], targetPeerId);
      };
    }
    return undefined;
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
   * Send a custom frame over the signalling socket. The frame is serialised
   * as `{ type, ...payload }`. The server must be configured to route this
   * frame type (polly does not interpret it). Returns true if the message
   * was sent, false if the connection is not open.
   *
   * Intended for application-level protocols that want to share the
   * existing signalling connection — for example, a pairing flow that
   * delivers a reciprocal token from the scanner back to the issuer.
   */
  sendCustom(type: string, payload: Record<string, unknown> = {}): boolean {
    if (!this.socket || this.socket.readyState !== this.WebSocketCtor.OPEN || !this.joined) {
      return false;
    }
    this.socket.send(JSON.stringify({ ...payload, type }));
    return true;
  }

  /**
   * Close the underlying WebSocket connection. The server's close handler
   * will evict this peer from its routing table. Also cancels any
   * pending reconnect attempt so the client stays closed until the
   * caller reopens it with another {@link connect} call.
   */
  close(): void {
    this.stopping = true;
    if (this.reconnectTimer) {
      clearTimeout(this.reconnectTimer);
      this.reconnectTimer = undefined;
    }
    this.socket?.close();
    this.socket = undefined;
    this.joined = false;
  }

  /** True if the signalling connection is open and joined. */
  get isConnected(): boolean {
    return this.joined && this.socket?.readyState === this.WebSocketCtor.OPEN;
  }
}
