/**
 * signalingServer — Phase 2 Elysia plugin that exposes a stateless
 * WebSocket route for SDP/ICE relay between $meshState peers.
 *
 * The mesh transport is a star-of-data-channels: peers establish direct
 * WebRTC connections to each other and exchange document operations
 * peer-to-peer once those channels are open. WebRTC connection setup
 * needs an out-of-band channel for SDP offer/answer and ICE candidate
 * exchange, and that channel is what this plugin provides. The plugin
 * does not own any document state, does not hold any encryption keys,
 * and never inspects the contents of the messages it relays. It is a
 * pure pub-sub by peer id.
 *
 * Once two peers have completed the SDP exchange and opened a direct
 * data channel, the signalling server is no longer on the critical
 * path — the peers talk directly. The signalling server's role is
 * therefore intermittent: peers connect to it only during the brief
 * windows when they are establishing or re-establishing connections.
 *
 * Wire protocol:
 *
 *   Client → server (join):
 *     { type: "join", peerId: "peer-alice" }
 *
 *   Client → server (signal to another peer):
 *     { type: "signal", peerId: "peer-alice", targetPeerId: "peer-bob",
 *       payload: { ... } }
 *
 *   Server → client (delivered signal):
 *     { type: "signal", peerId: "peer-alice", targetPeerId: "peer-bob",
 *       payload: { ... } }
 *
 *   Server → client (notification of unknown target):
 *     { type: "error", reason: "unknown-target", targetPeerId: "..." }
 *
 * The `payload` is opaque to the signalling server — typically it
 * carries an SDP offer, SDP answer, or ICE candidate. Applications can
 * also use the relay for any other peer-to-peer message that needs an
 * intermediary, such as the initial handshake of a pairing flow.
 *
 * @example
 * ```ts
 * import { Elysia } from "elysia";
 * import { signalingServer } from "@fairfox/polly/elysia";
 *
 * const app = new Elysia()
 *   .use(signalingServer({ path: "/polly/signaling" }))
 *   .listen(8080);
 * ```
 */

import { Elysia } from "elysia";
import { isRecord, readString } from "../shared/lib/guards";

/** A signalling message. The `type` discriminates between client-to-server
 * requests (join, signal), the error envelope, and the server-to-client
 * discovery frames (peers-present, peer-joined, peer-left) that let
 * peers learn about each other without polling. */
export type SignalingMessage =
  | {
      type: "join";
      /** The peer registering itself with the signalling server. */
      peerId: string;
    }
  | {
      type: "signal";
      /** The peer sending the signal. */
      peerId: string;
      /** The peer the signal is being relayed to. */
      targetPeerId: string;
      /** Opaque payload, typically SDP or ICE. */
      payload: unknown;
    }
  | {
      type: "error";
      reason: "unknown-target" | "not-joined" | "malformed";
      targetPeerId?: string;
    }
  | {
      /** Sent to a newcomer immediately after it joins, listing every
       * peer that was already joined at that moment. Empty for a lone
       * newcomer. */
      type: "peers-present";
      peerIds: string[];
    }
  | {
      /** Broadcast to every incumbent when a new peer joins. */
      type: "peer-joined";
      peerId: string;
    }
  | {
      /** Broadcast to every remaining incumbent when a joined peer
       * closes its socket. Never emitted for a connection that never
       * sent a join frame. */
      type: "peer-left";
      peerId: string;
    };

/** A frame whose `type` is outside the built-in signalling vocabulary.
 * Consumers who pass an {@link SignalingServerOptions.onCustomFrame}
 * handler receive these on the server side; everything else — including
 * routing them to a specific peer, storing a session, or rejecting the
 * frame — is the consumer's call. Polly does not touch the body. */
export interface CustomSignalingFrame {
  type: string;
  [key: string]: unknown;
}

/** Minimal surface the custom-frame handler receives in place of the
 * Elysia-specific `ws` object so the plugin stays portable. Exposes the
 * `data` bag (used to stash the authenticated peerId under the existing
 * join handshake) and a `send` method. */
export interface CustomFrameSocket {
  data: Record<string, unknown>;
  send: (msg: unknown) => void;
}

export interface SignalingServerOptions {
  /** WebSocket route path. Defaults to "/polly/signaling". */
  path?: string;
  /** Optional hook for frames whose `type` is outside the built-in
   * vocabulary. The plugin invokes it in place of returning a
   * `malformed` error, so consumers can layer their own application
   * protocol (pairing return tokens, presence pings, etc.) on the
   * existing socket. The `peerId` argument is the sender's
   * authenticated peer id from their prior `join` frame, or
   * `undefined` if they haven't joined yet. */
  onCustomFrame?: (
    socket: CustomFrameSocket,
    frame: CustomSignalingFrame,
    peerId: string | undefined
  ) => void;
}

/** The part of an Elysia WebSocket the plugin uses. Elysia's `ws`
 * satisfies it: its `data` bag is an object literal type, so it fits the
 * index signature on {@link CustomFrameSocket}. */
type SignalingSocket = CustomFrameSocket & { readonly readyState: number };

const OPEN = 1;

/** Decode an incoming frame. Elysia parses JSON text frames itself, so
 * `raw` is usually already an object; a string is parsed here. */
function decodeFrame(raw: unknown): Record<string, unknown> | undefined {
  if (typeof raw !== "string") return isRecord(raw) ? raw : undefined;
  try {
    const parsed: unknown = JSON.parse(raw);
    return isRecord(parsed) ? parsed : undefined;
  } catch {
    return undefined;
  }
}

/** The peer id a socket joined with. Elysia keeps one `data` bag per
 * connection across callbacks, so the id lives there. */
function joinedPeerId(ws: SignalingSocket): string | undefined {
  return readString(ws.data["peerId"]);
}

/**
 * Construct the signalling-server Elysia plugin. The plugin keeps a
 * per-instance map of peer id → WebSocket connection so that incoming
 * "signal" messages can be routed to the right target socket. The map
 * is local to the plugin instance, not shared across processes; for
 * multi-instance deployments behind a load balancer, applications need
 * sticky connection routing or a shared backplane (Redis pub-sub or
 * similar). That is a follow-up.
 */
export function signalingServer(options: SignalingServerOptions = {}) {
  const path = options.path ?? "/polly/signaling";
  const onCustomFrame = options.onCustomFrame;
  // Per-peer-id map of joined sockets. The inverse mapping is stored
  // directly on ws.data (a mutable property bag that Elysia preserves
  // across message callbacks for a given connection); the webrtc-p2p-chat
  // example in examples/ confirms this pattern is stable under Bun.
  const peerSockets = new Map<string, SignalingSocket>();

  const send = (ws: SignalingSocket, msg: SignalingMessage): void => {
    ws.send(msg);
  };

  const handleJoin = (ws: SignalingSocket, peerId: string): void => {
    // Collect the peers that were already joined so we can (a) tell the
    // newcomer who is present and (b) tell each of them about the
    // newcomer. A rejoin with the same peerId replaces the prior entry
    // but is otherwise treated as a fresh arrival.
    const incumbents: Array<{ peerId: string; socket: SignalingSocket }> = [];
    for (const [existingPeerId, existingSocket] of peerSockets) {
      if (existingPeerId === peerId) continue;
      incumbents.push({ peerId: existingPeerId, socket: existingSocket });
    }
    peerSockets.set(peerId, ws);
    ws.data["peerId"] = peerId;

    send(ws, { type: "peers-present", peerIds: incumbents.map((i) => i.peerId) });

    for (const incumbent of incumbents) {
      try {
        send(incumbent.socket, { type: "peer-joined", peerId });
      } catch {
        // If a send fails we leave the stale socket to its own close
        // handler to evict. Dropping here would open a window where
        // the next signal to this peer still thinks it's alive.
      }
    }
  };

  const sendUnknownTarget = (ws: SignalingSocket, targetPeerId: string): void => {
    send(ws, { type: "error", reason: "unknown-target", targetPeerId });
  };

  /** Look up a target socket and confirm it is still open. */
  const findOpenTarget = (targetPeerId: string): SignalingSocket | undefined => {
    const target = peerSockets.get(targetPeerId);
    if (!target) return undefined;
    if (target.readyState !== OPEN) {
      peerSockets.delete(targetPeerId);
      return undefined;
    }
    return target;
  };

  const handleSignal = (ws: SignalingSocket, frame: Record<string, unknown>): void => {
    const senderId = joinedPeerId(ws);
    if (!senderId) {
      send(ws, { type: "error", reason: "not-joined" });
      return;
    }
    const targetPeerId = readString(frame["targetPeerId"]);
    if (targetPeerId === undefined) {
      send(ws, { type: "error", reason: "malformed" });
      return;
    }
    const target = findOpenTarget(targetPeerId);
    if (!target) {
      sendUnknownTarget(ws, targetPeerId);
      return;
    }
    try {
      send(target, { type: "signal", peerId: senderId, targetPeerId, payload: frame["payload"] });
    } catch {
      peerSockets.delete(targetPeerId);
      sendUnknownTarget(ws, targetPeerId);
    }
  };

  // Intentionally unnamed — Elysia deduplicates plugins by name, and each
  // signalingServer() call needs its own closure-captured peer map.
  return new Elysia().ws(path, {
    message(ws, raw) {
      const frame = decodeFrame(raw);
      const type = readString(frame?.["type"]);
      if (frame === undefined || type === undefined) {
        send(ws, { type: "error", reason: "malformed" });
        return;
      }
      if (type === "join") {
        const peerId = readString(frame["peerId"]);
        if (peerId === undefined) {
          send(ws, { type: "error", reason: "malformed" });
          return;
        }
        handleJoin(ws, peerId);
        return;
      }
      if (type === "signal") {
        handleSignal(ws, frame);
        return;
      }
      // Unknown types route to the consumer's custom-frame hook when
      // one is configured. Without a hook they still fall through to
      // the `malformed` error — same behaviour as before this branch
      // existed.
      if (onCustomFrame !== undefined) {
        onCustomFrame(ws, { ...frame, type }, joinedPeerId(ws));
        return;
      }
      send(ws, { type: "error", reason: "malformed" });
    },

    close(ws) {
      const peerId = joinedPeerId(ws);
      if (!peerId) {
        // Connection that never sent a join — nothing to broadcast and
        // nothing to evict. A bystander coming and going leaves no trace.
        return;
      }
      // Only evict if the map still points at *this* socket. A stale
      // close after the same peerId rejoined on a new socket should not
      // take the fresh entry with it. The comparison uses the `data` bag
      // Elysia attaches to each connection because it is preserved across
      // message and close callbacks, unlike the `ws` wrapper object which
      // Elysia may or may not reuse.
      const mapped = peerSockets.get(peerId);
      if (mapped === undefined || mapped.data !== ws.data) {
        return;
      }
      peerSockets.delete(peerId);
      for (const incumbentSocket of peerSockets.values()) {
        try {
          send(incumbentSocket, { type: "peer-left", peerId });
        } catch {
          // Incumbent socket is gone; its own close handler will tidy.
        }
      }
    },
  });
}
