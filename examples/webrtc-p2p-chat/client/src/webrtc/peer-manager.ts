import { displayName, isSignalingConnected, messages, peerId, peers } from "../state";
import type { ChatMessage, P2PMessage } from "../types";
import { PeerConnection } from "./peer-connection";
import { SignalingClient } from "./signaling-client";

/**
 * PeerManager - Coordinates signaling and peer connections
 *
 * Responsibilities:
 * - Manage signaling client
 * - Create/destroy peer connections
 * - Handle WebRTC signaling flow
 * - Route P2P messages to handlers
 * - Update Polly state
 */
export class PeerManager {
  private connections = new Map<string, PeerConnection>();
  private signaling: SignalingClient;
  private currentRoomId: string | null = null;

  constructor(signalingUrl: string) {
    this.signaling = new SignalingClient(signalingUrl);
    this.setupSignalingHandlers();
  }

  /**
   * Connect to signaling server
   */
  async connect() {
    await this.signaling.connect();
    isSignalingConnected.value = true;
  }

  /**
   * Join a room
   */
  joinRoom(roomId: string) {
    this.currentRoomId = roomId;
    this.signaling.send({
      type: "join_room",
      roomId,
      peerId: peerId.value,
      displayName: displayName.value,
    });
  }

  /**
   * Leave current room
   */
  leaveRoom() {
    if (!this.currentRoomId) return;

    this.signaling.send({
      type: "leave_room",
      roomId: this.currentRoomId,
      peerId: peerId.value,
    });

    // Close all peer connections
    for (const conn of this.connections.values()) {
      conn.close();
    }
    this.connections.clear();

    // Clear state
    peers.value = [];
    this.currentRoomId = null;
  }

  /**
   * Send a chat message to all connected peers
   */
  sendMessage(text: string) {
    const message: ChatMessage = {
      id: crypto.randomUUID(),
      text,
      from: peerId.value,
      fromName: displayName.value,
      timestamp: Date.now(),
      delivered: false,
    };

    // Add to local messages
    messages.value = [...messages.value, message];

    // Send to all connected peers via P2P
    const p2pMessage: P2PMessage = {
      type: "chat_message",
      id: message.id,
      text,
      timestamp: message.timestamp,
      from: peerId.value,
    };

    let sentCount = 0;
    for (const conn of this.connections.values()) {
      if (conn.connectionState === "connected") {
        conn.send(p2pMessage);
        sentCount++;
      }
    }

    // Mark as delivered if sent to at least one peer
    messages.value = messages.value.map((m) =>
      m.id === message.id ? { ...m, delivered: sentCount > 0 } : m
    );
  }

  /**
   * Disconnect from signaling and close all connections
   */
  disconnect() {
    this.leaveRoom();
    this.signaling.disconnect();
    isSignalingConnected.value = false;
  }

  /**
   * Set up signaling message handlers
   */
  private setupSignalingHandlers() {
    this.signaling.onMessage((message) => {
      switch (message.type) {
        case "room_joined":
          // Connect to all existing peers (we initiate)
          for (const peer of message.peers) {
            this.connectToPeer(peer.id, peer.displayName, true);
          }
          break;

        case "peer_joined":
          // New peer joined - wait for them to send offer
          // (they initiate since they joined after us)
          this.addPeer(message.peer.id, message.peer.displayName);
          break;

        case "peer_left":
          this.removePeer(message.peerId);
          break;

        case "offer":
          this.handleOffer(message.from, message.offer);
          break;

        case "answer":
          this.handleAnswer(message.from, message.answer);
          break;

        case "ice_candidate":
          this.handleIceCandidate(message.from, message.candidate);
          break;
      }
    });
  }

  /**
   * Create a new peer connection
   */
  private connectToPeer(remotePeerId: string, remoteName: string, initiator: boolean) {
    if (this.connections.has(remotePeerId)) {
      console.log(`Already connected to ${remotePeerId}`);
      return;
    }

    const conn = new PeerConnection({
      peerId: remotePeerId,
      displayName: remoteName,
      initiator,

      onMessage: (message) => {
        this.handleP2PMessage(remotePeerId, message);
      },

      onStateChange: (state) => {
        this.updatePeerState(remotePeerId, { connectionState: state });

        if (state === "failed" || state === "closed") {
          this.removePeer(remotePeerId);
        }
      },

      onIceCandidate: (candidate) => {
        this.signaling.send({
          type: "ice_candidate",
          from: peerId.value,
          to: remotePeerId,
          candidate,
        });
      },
    });

    this.connections.set(remotePeerId, conn);
    this.addPeer(remotePeerId, remoteName);

    // If we're the initiator, create and send offer
    if (initiator) {
      conn.createOffer().then((offer) => {
        this.signaling.send({
          type: "offer",
          from: peerId.value,
          to: remotePeerId,
          offer,
        });
      });
    }
  }

  /**
   * Handle incoming WebRTC offer
   */
  private async handleOffer(fromPeerId: string, offer: RTCSessionDescriptionInit) {
    let conn = this.connections.get(fromPeerId);

    if (!conn) {
      // Create connection if we don't have one yet
      const peerInfo = peers.value.find((p) => p.id === fromPeerId);
      this.connectToPeer(fromPeerId, peerInfo?.displayName || "Unknown", false);
      conn = this.connections.get(fromPeerId)!;
    }

    const answer = await conn.handleOffer(offer);

    this.signaling.send({
      type: "answer",
      from: peerId.value,
      to: fromPeerId,
      answer,
    });
  }

  /**
   * Handle incoming WebRTC answer
   */
  private handleAnswer(fromPeerId: string, answer: RTCSessionDescriptionInit) {
    const conn = this.connections.get(fromPeerId);
    if (conn) {
      conn.handleAnswer(answer);
    }
  }

  /**
   * Handle incoming ICE candidate
   */
  private handleIceCandidate(fromPeerId: string, candidate: RTCIceCandidateInit) {
    const conn = this.connections.get(fromPeerId);
    if (conn) {
      conn.addIceCandidate(candidate);
    }
  }

  /**
   * Add peer to state
   */
  private addPeer(id: string, name: string) {
    if (!peers.value.find((p) => p.id === id)) {
      peers.value = [
        ...peers.value,
        {
          id,
          displayName: name,
          connectionState: "new",
          connectedAt: Date.now(),
        },
      ];
    }
  }

  /**
   * Remove peer from state
   */
  private removePeer(id: string) {
    const conn = this.connections.get(id);
    if (conn) {
      conn.close();
      this.connections.delete(id);
    }

    peers.value = peers.value.filter((p) => p.id !== id);
  }

  /**
   * Update peer state
   */
  private updatePeerState(id: string, updates: Partial<(typeof peers.value)[0]>) {
    peers.value = peers.value.map((p) => (p.id === id ? { ...p, ...updates } : p));
  }

  /**
   * Handle incoming P2P message
   */
  private handleP2PMessage(fromPeerId: string, message: P2PMessage) {
    const peer = peers.value.find((p) => p.id === fromPeerId);

    switch (message.type) {
      case "chat_message":
        messages.value = [
          ...messages.value,
          {
            id: message.id,
            text: message.text,
            from: fromPeerId,
            fromName: peer?.displayName || "Unknown",
            timestamp: message.timestamp,
            delivered: true,
          },
        ];
        break;

      case "ping": {
        // Send pong back
        const conn = this.connections.get(fromPeerId);
        conn?.send({ type: "pong", timestamp: Date.now() });
        break;
      }

      case "pong": {
        // Calculate latency
        const latency = Date.now() - message.timestamp;
        this.updatePeerState(fromPeerId, { latency });
        break;
      }

      case "typing_indicator":
        // Could implement typing indicators here
        break;
    }
  }
}
