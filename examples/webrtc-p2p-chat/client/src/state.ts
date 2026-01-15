import { $syncedState, $state } from '@fairfox/polly/state';
import type { Peer, ChatMessage, Room } from './types';

/**
 * Polly State Management for WebRTC P2P Chat
 *
 * This example uses Polly's state primitives to manage local application state.
 * Unlike other examples where state syncs across the network, here Polly only
 * manages local UI state and persistence - actual messages travel P2P via WebRTC!
 */

// Current room (persisted locally)
export const currentRoom = $syncedState<Room | null>('room', null);

// User identity (persisted locally)
export const displayName = $syncedState<string>('displayName', '');
export const peerId = $syncedState<string>('peerId', crypto.randomUUID());

// Peers in current room (synced across components, not persisted)
export const peers = $syncedState<Peer[]>('peers', []);

// Chat messages (persisted locally)
export const messages = $syncedState<ChatMessage[]>('messages', []);

// Connection state (ephemeral - not persisted)
export const isConnected = $state(false);
export const isSignalingConnected = $state(false);

// Typing indicators (ephemeral)
export const typingPeers = $state<Set<string>>(new Set());

// UI state (ephemeral)
export const isTyping = $state(false);
