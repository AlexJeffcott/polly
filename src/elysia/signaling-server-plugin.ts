// @ts-nocheck - Optional peer dependencies (elysia, @elysiajs/eden)
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

/** A signalling message. The `type` discriminates between join (peer
 * registration), signal (relayed message), and error (server response). */
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
    };

export interface SignalingServerOptions {
  /** WebSocket route path. Defaults to "/polly/signaling". */
  path?: string;
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
  // Per-peer-id map of joined sockets. The inverse mapping is stored
  // directly on ws.data (a mutable property bag that Elysia preserves
  // across message callbacks for a given connection); the webrtc-p2p-chat
  // example in examples/ confirms this pattern is stable under Bun.
  const peerSockets = new Map<string, { send: (msg: unknown) => void }>();

  // Intentionally unnamed — Elysia deduplicates plugins by name, and each
  // signalingServer() call needs its own closure-captured peer map.
  const parseMessage = (raw: unknown): SignalingMessage | undefined => {
    try {
      return typeof raw === "string" ? JSON.parse(raw) : (raw as unknown as SignalingMessage);
    } catch {
      return undefined;
    }
  };

  const handleJoin = (ws: unknown, peerId: string): void => {
    peerSockets.set(peerId, ws as unknown as { send: (m: unknown) => void });
    const wsWithData = ws as unknown as { data: Record<string, unknown> };
    wsWithData.data.peerId = peerId;
  };

  const sendUnknownTarget = (ws: unknown, targetPeerId: string): void => {
    (ws as unknown as { send: (m: unknown) => void }).send({
      type: "error",
      reason: "unknown-target",
      targetPeerId,
    } as unknown as SignalingMessage);
  };

  /** Look up a target socket and confirm it is still open. */
  const findOpenTarget = (targetPeerId: string): { send: (msg: unknown) => void } | undefined => {
    const target = peerSockets.get(targetPeerId);
    if (!target) return undefined;
    const readyState = (target as unknown as { readyState?: number }).readyState;
    const OPEN = 1;
    if (readyState !== undefined && readyState !== OPEN) {
      peerSockets.delete(targetPeerId);
      return undefined;
    }
    return target;
  };

  const handleSignal = (ws: unknown, msg: Extract<SignalingMessage, { type: "signal" }>): void => {
    const wsWithData = ws as unknown as {
      data: Record<string, unknown>;
      send: (m: unknown) => void;
    };
    const senderId = wsWithData.data.peerId as unknown as string | undefined;
    if (!senderId) {
      wsWithData.send({ type: "error", reason: "not-joined" } as unknown as SignalingMessage);
      return;
    }
    const target = findOpenTarget(msg.targetPeerId);
    if (!target) {
      sendUnknownTarget(ws, msg.targetPeerId);
      return;
    }
    const relayed: SignalingMessage = {
      type: "signal",
      peerId: senderId,
      targetPeerId: msg.targetPeerId,
      payload: msg.payload,
    };
    try {
      target.send(relayed);
    } catch {
      peerSockets.delete(msg.targetPeerId);
      sendUnknownTarget(ws, msg.targetPeerId);
    }
  };

  return new Elysia().ws(path, {
    message(ws, raw) {
      const msg = parseMessage(raw);
      if (!msg) {
        ws.send({ type: "error", reason: "malformed" } as unknown as SignalingMessage);
        return;
      }
      if (msg.type === "join") {
        handleJoin(ws, msg.peerId);
        return;
      }
      if (msg.type === "signal") {
        handleSignal(ws, msg);
        return;
      }
      ws.send({ type: "error", reason: "malformed" } as unknown as SignalingMessage);
    },

    close(ws) {
      const peerId = (ws.data as unknown as Record<string, unknown>).peerId as unknown as
        | string
        | undefined;
      if (peerId) {
        // Only delete the entry if it still points at *this* socket, so a
        // stale close after a reconnect does not evict the new socket.
        if (peerSockets.get(peerId) === (ws as unknown as { send: (m: unknown) => void })) {
          peerSockets.delete(peerId);
        }
      }
    },
  });
}
