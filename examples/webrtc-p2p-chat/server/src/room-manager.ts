import type { ServerWebSocket } from "bun";
import type { PeerInfo, SignalingMessage } from "./types";

/**
 * RoomManager - Manages rooms and peer connections for WebRTC signaling
 *
 * Responsibilities:
 * - Track which peers are in which rooms
 * - Relay signaling messages between peers
 * - Handle peer join/leave events
 * - Clean up on disconnect
 */

interface PeerConnection {
  id: string;
  displayName: string;
  ws: ServerWebSocket<unknown>;
  joinedAt: number;
}

export class RoomManager {
  // Map of roomId -> Map of peerId -> PeerConnection
  private rooms = new Map<string, Map<string, PeerConnection>>();

  // Reverse map: wsId -> { roomId, peerId } for cleanup
  private wsToRoom = new Map<number | string, { roomId: string; peerId: string }>();

  /**
   * Add a peer to a room
   */
  joinRoom(roomId: string, peer: PeerConnection) {
    // Create room if it doesn't exist
    if (!this.rooms.has(roomId)) {
      this.rooms.set(roomId, new Map());
      console.log(`📦 Created room: ${roomId}`);
    }

    const room = this.rooms.get(roomId)!;
    room.set(peer.id, peer);

    // Track WebSocket for cleanup
    this.wsToRoom.set(peer.ws.data as string, { roomId, peerId: peer.id });

    console.log(`👤 ${peer.displayName} (${peer.id}) joined room ${roomId}`);
    console.log(`   Room ${roomId} now has ${room.size} peer(s)`);
  }

  /**
   * Remove a peer from a room
   */
  leaveRoom(roomId: string, peerId: string) {
    const room = this.rooms.get(roomId);
    if (!room) return;

    const peer = room.get(peerId);
    room.delete(peerId);

    if (peer) {
      this.wsToRoom.delete(peer.ws.data as string);
      console.log(`👋 ${peer.displayName} (${peerId}) left room ${roomId}`);
    }

    // Clean up empty rooms
    if (room.size === 0) {
      this.rooms.delete(roomId);
      console.log(`🗑️  Room ${roomId} is now empty, removed`);
    } else {
      console.log(`   Room ${roomId} now has ${room.size} peer(s)`);
    }
  }

  /**
   * Get all peers in a room (optionally excluding one peer)
   */
  getPeers(roomId: string, excludePeerId?: string): PeerInfo[] {
    const room = this.rooms.get(roomId);
    if (!room) return [];

    return Array.from(room.values())
      .filter((p) => p.id !== excludePeerId)
      .map((p) => ({
        id: p.id,
        displayName: p.displayName,
        joinedAt: p.joinedAt,
      }));
  }

  /**
   * Send a message to a specific peer
   */
  sendToPeer(peerId: string, message: SignalingMessage): boolean {
    // Find peer in any room
    for (const room of this.rooms.values()) {
      const peer = room.get(peerId);
      if (peer) {
        try {
          peer.ws.send(JSON.stringify(message));
          return true;
        } catch (error) {
          console.error(`Failed to send to peer ${peerId}:`, error);
          return false;
        }
      }
    }

    console.warn(`⚠️  Peer ${peerId} not found for message relay`);
    return false;
  }

  /**
   * Broadcast a message to all peers in a room (optionally excluding one)
   */
  broadcast(roomId: string, message: SignalingMessage, excludePeerId?: string) {
    const room = this.rooms.get(roomId);
    if (!room) {
      console.warn(`⚠️  Room ${roomId} not found for broadcast`);
      return;
    }

    let sentCount = 0;
    for (const [peerId, peer] of room) {
      if (peerId !== excludePeerId) {
        try {
          peer.ws.send(JSON.stringify(message));
          sentCount++;
        } catch (error) {
          console.error(`Failed to broadcast to peer ${peerId}:`, error);
        }
      }
    }

    console.log(`📢 Broadcast to ${sentCount} peer(s) in room ${roomId}`);
  }

  /**
   * Clean up when a WebSocket disconnects
   */
  cleanup(wsId: number | string) {
    const entry = this.wsToRoom.get(wsId);
    if (!entry) return;

    const { roomId, peerId } = entry;
    this.leaveRoom(roomId, peerId);

    // Notify others in the room
    this.broadcast(roomId, {
      type: "peer_left",
      peerId,
    });
  }

  /**
   * Get statistics about rooms and peers
   */
  getStats() {
    const roomCount = this.rooms.size;
    let totalPeers = 0;

    for (const room of this.rooms.values()) {
      totalPeers += room.size;
    }

    return {
      roomCount,
      totalPeers,
      rooms: Array.from(this.rooms.entries()).map(([roomId, peers]) => ({
        roomId,
        peerCount: peers.size,
        peers: Array.from(peers.values()).map((p) => ({
          id: p.id,
          displayName: p.displayName,
        })),
      })),
    };
  }
}
