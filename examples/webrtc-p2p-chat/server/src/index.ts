import { cors } from "@elysiajs/cors";
import { Elysia } from "elysia";
import { RoomManager } from "./room-manager";
import type { SignalingMessage } from "./types";

/**
 * WebRTC P2P Chat - Signaling Server
 *
 * This server only handles signaling (helping peers find each other).
 * It NEVER sees actual chat messages - those travel directly P2P!
 *
 * Responsibilities:
 * - Manage rooms and peer membership
 * - Relay WebRTC signaling messages (SDP offers/answers, ICE candidates)
 * - Notify peers when others join/leave
 */

const roomManager = new RoomManager();

const app = new Elysia()
  .use(
    cors({
      origin: true,
      credentials: true,
    })
  )

  // Health check endpoint
  .get("/health", () => {
    const stats = roomManager.getStats();
    return {
      status: "ok",
      uptime: process.uptime(),
      timestamp: Date.now(),
      ...stats,
    };
  })

  // Statistics endpoint (for debugging)
  .get("/stats", () => {
    return roomManager.getStats();
  })

  // WebSocket signaling endpoint
  .ws("/signaling", {
    // Assign unique ID to each connection
    open(ws) {
      // Store connection ID in ws.data for tracking
      const wsId = crypto.randomUUID();
      (ws.data as any) = wsId;
      console.log(`🔌 WebSocket connected: ${wsId}`);
    },

    message(ws, message) {
      try {
        const msg =
          typeof message === "string" ? JSON.parse(message) : (message as SignalingMessage);

        const wsId = ws.data as any;
        console.log(`📨 Received: ${msg.type} from ${wsId}`);

        switch (msg.type) {
          case "join_room":
            handleJoinRoom(ws, msg);
            break;

          case "leave_room":
            handleLeaveRoom(msg);
            break;

          case "offer":
          case "answer":
          case "ice_candidate":
            handleSignalingMessage(msg);
            break;

          default:
            console.warn(`⚠️  Unknown message type:`, msg);
        }
      } catch (error) {
        console.error("❌ Error processing message:", error);
        ws.send(
          JSON.stringify({
            type: "connection_failed",
            peerId: "",
            error: "Invalid message format",
          })
        );
      }
    },

    close(ws) {
      const wsId = ws.data as any;
      console.log(`🔌 WebSocket disconnected: ${wsId}`);
      roomManager.cleanup(wsId);
    },
  })

  .listen(3001);

/**
 * Handle peer joining a room
 */
function handleJoinRoom(ws: any, msg: Extract<SignalingMessage, { type: "join_room" }>) {
  const { roomId, peerId, displayName } = msg;

  // Get current peers before adding new one
  const existingPeers = roomManager.getPeers(roomId);

  // Add peer to room
  roomManager.joinRoom(roomId, {
    id: peerId,
    displayName,
    ws,
    joinedAt: Date.now(),
  });

  // Send existing peers to new peer
  ws.send(
    JSON.stringify({
      type: "room_joined",
      roomId,
      peers: existingPeers,
    } satisfies SignalingMessage)
  );

  // Notify existing peers about new peer
  roomManager.broadcast(
    roomId,
    {
      type: "peer_joined",
      peer: {
        id: peerId,
        displayName,
        joinedAt: Date.now(),
      },
    },
    peerId
  ); // Exclude the new peer
}

/**
 * Handle peer leaving a room
 */
function handleLeaveRoom(msg: Extract<SignalingMessage, { type: "leave_room" }>) {
  const { roomId, peerId } = msg;

  roomManager.leaveRoom(roomId, peerId);

  // Notify others
  roomManager.broadcast(roomId, {
    type: "peer_left",
    peerId,
  });
}

/**
 * Handle WebRTC signaling messages (relay to target peer)
 */
function handleSignalingMessage(
  msg: Extract<SignalingMessage, { type: "offer" | "answer" | "ice_candidate" }>
) {
  const success = roomManager.sendToPeer(msg.to, msg);

  if (!success) {
    console.warn(`⚠️  Failed to relay ${msg.type} from ${msg.from} to ${msg.to}`);
  }
}

console.log(`🎯 Signaling server running at ${app.server?.hostname}:${app.server?.port}`);
console.log(`   WebSocket: ws://${app.server?.hostname}:${app.server?.port}/signaling`);
console.log(`   Health: http://${app.server?.hostname}:${app.server?.port}/health`);
console.log(`   Stats: http://${app.server?.hostname}:${app.server?.port}/stats`);
console.log();
console.log("💡 Server is ready for WebRTC signaling (NO chat data stored!)");
