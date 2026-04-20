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
    const newcomer = ws as unknown as { send: (m: unknown) => void };
    // Collect the peers that were already joined so we can (a) tell the
    // newcomer who is present and (b) tell each of them about the
    // newcomer. A rejoin with the same peerId replaces the prior entry
    // but is otherwise treated as a fresh arrival.
    const incumbents: Array<{ peerId: string; socket: { send: (m: unknown) => void } }> = [];
    for (const [existingPeerId, existingSocket] of peerSockets) {
      if (existingPeerId === peerId) continue;
      incumbents.push({ peerId: existingPeerId, socket: existingSocket });
    }
    peerSockets.set(peerId, newcomer);
    const wsWithData = ws as unknown as { data: Record<string, unknown> };
    wsWithData.data.peerId = peerId;

    newcomer.send({
      type: "peers-present",
      peerIds: incumbents.map((i) => i.peerId),
    } as unknown as SignalingMessage);

    for (const incumbent of incumbents) {
      try {
        incumbent.socket.send({ type: "peer-joined", peerId } as unknown as SignalingMessage);
      } catch {
        // If a send fails we leave the stale socket to its own close
        // handler to evict. Dropping here would open a window where
        // the next signal to this peer still thinks it's alive.
      }
    }
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
      // Unknown types route to the consumer's custom-frame hook when
      // one is configured. Without a hook they still fall through to
      // the `malformed` error — same behaviour as before this branch
      // existed.
      if (onCustomFrame !== undefined) {
        const wsWithData = ws as unknown as CustomFrameSocket;
        const senderId = wsWithData.data["peerId"];
        const peerId = typeof senderId === "string" ? senderId : undefined;
        onCustomFrame(wsWithData, msg as unknown as CustomSignalingFrame, peerId);
        return;
      }
      ws.send({ type: "error", reason: "malformed" } as unknown as SignalingMessage);
    },

    close(ws) {
      const peerId = (ws.data as unknown as Record<string, unknown>).peerId as unknown as
        | string
        | undefined;
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
      const wsData = (ws as unknown as { data: Record<string, unknown> }).data;
      const mappedData = (mapped as unknown as { data?: Record<string, unknown> } | undefined)
        ?.data;
      if (mapped === undefined || mappedData !== wsData) {
        return;
      }
      peerSockets.delete(peerId);
      for (const [_incumbentId, incumbentSocket] of peerSockets) {
        try {
          incumbentSocket.send({ type: "peer-left", peerId } as unknown as SignalingMessage);
        } catch {
          // Incumbent socket is gone; its own close handler will tidy.
        }
      }
    },
  });
}
