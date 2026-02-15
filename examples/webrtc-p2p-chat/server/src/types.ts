/**
 * Signaling Message Types for WebRTC P2P Chat
 *
 * These messages are exchanged between clients and the signaling server
 * to establish WebRTC connections. The server NEVER sees actual chat
 * messages - those travel directly peer-to-peer over data channels.
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
