import { $sharedState, $state, $syncedState } from "@fairfox/polly/state";
import type { ChatMessage, Peer, Room } from "./types";

/**
 * Polly State Management for WebRTC P2P Chat
 *
 * This example uses Polly's state primitives to manage local application state.
 * Unlike other examples where state syncs across the network, here Polly only
 * manages local UI state and persistence - actual messages travel P2P via WebRTC!
 */

// Current room (persisted locally, verified for TLA+ generation)
export const currentRoom = $syncedState<Room | null>("room", null);

// User identity
// displayName persists so you don't have to re-enter it
export const displayName = $syncedState<string>("displayName", "");

// IMPORTANT: peerId must be ephemeral (per-tab) so multiple tabs don't conflict
// Each browser tab = separate peer with unique ID
export const peerId = $state<string>(crypto.randomUUID());

// Peers in current room (synced across components, not persisted)
export const peers = $syncedState<Peer[]>("peers", []);

// Verified peer count (exercises { type: "number" } verification)
export const peerCount = $sharedState("peerCount", 0, { verify: true });

// Chat messages (persisted locally)
export const messages = $syncedState<ChatMessage[]>("messages", []);

// Connection state (ephemeral - not persisted)
export const isConnected = $state(false);
export const isSignalingConnected = $state(false);

// Typing indicators (ephemeral)
export const typingPeers = $state<Set<string>>(new Set());

// UI state (ephemeral)
export const isTyping = $state(false);
