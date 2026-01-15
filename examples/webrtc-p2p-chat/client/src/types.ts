/**
 * Types for WebRTC P2P Chat Example
 */

// Messages sent P2P over WebRTC data channels
export type P2PMessage =
  | { type: 'chat_message'; id: string; text: string; timestamp: number; from: string }
  | { type: 'typing_indicator'; isTyping: boolean; from: string }
  | { type: 'ping'; timestamp: number }
  | { type: 'pong'; timestamp: number }

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
