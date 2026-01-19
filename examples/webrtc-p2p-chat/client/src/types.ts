/**
 * Types for WebRTC P2P Chat Example
 */

// Messages sent between client and server for WebRTC signaling
export type SignalingMessage =
  // Room management
  | { type: "join_room"; roomId: string; peerId: string; displayName: string }
  | { type: "leave_room"; roomId: string; peerId: string }

  // Peer discovery
  | { type: "room_joined"; roomId: string; peers: PeerInfo[] }
  | { type: "peer_joined"; peer: PeerInfo }
  | { type: "peer_left"; peerId: string }

  // WebRTC signaling (SDP offer/answer exchange)
  | { type: "offer"; from: string; to: string; offer: RTCSessionDescriptionInit }
  | { type: "answer"; from: string; to: string; answer: RTCSessionDescriptionInit }
  | { type: "ice_candidate"; from: string; to: string; candidate: RTCIceCandidateInit }

  // Connection events
  | { type: "connection_failed"; peerId: string; error: string };

export interface PeerInfo {
  id: string;
  displayName: string;
  joinedAt: number;
}

// Messages sent P2P over WebRTC data channels
export type P2PMessage =
  | { type: "chat_message"; id: string; text: string; timestamp: number; from: string }
  | { type: "typing_indicator"; isTyping: boolean; from: string }
  | { type: "ping"; timestamp: number }
  | { type: "pong"; timestamp: number };

export interface Peer {
  id: string;
  displayName: string;
  connectionState: RTCPeerConnectionState;
  latency?: number; // ms, calculated from ping/pong
  connectedAt: number;
}

export interface ChatMessage {
  id: string;
  text: string;
  from: string;
  fromName: string;
  timestamp: number;
  delivered: boolean;
}

export interface Room {
  id: string;
  joinedAt: number;
}
