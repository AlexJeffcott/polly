// State-mutating functions with verification primitives
// Demonstrates requires/ensures and parameter tracing for WebRTC state management
import { ensures, requires } from "@fairfox/polly/verify";
import { currentRoom, peerCount, peers } from "./state";
import type { Room } from "./types";

export function joinRoom(roomId: string, displayName: string) {
  requires(currentRoom.value === null, "Must not be in a room to join");

  const room: Room = { id: roomId, joinedAt: Date.now() };
  currentRoom.value = room;

  ensures(currentRoom.value !== null, "Must be in a room after joining");
}

export function leaveRoom() {
  requires(currentRoom.value !== null, "Must be in a room to leave");

  currentRoom.value = null;
  peers.value = [];
  peerCount.value = 0;

  ensures(currentRoom.value === null, "Must not be in a room after leaving");
  ensures(peerCount.value === 0, "Peer count must be zero after leaving");
}

// The isOnline boolean parameter exercises parameter tracing for TLA+ generation
export function peerConnected(isOnline: boolean) {
  requires(currentRoom.value !== null, "Must be in a room for peer events");

  if (isOnline) {
    peerCount.value += 1;
  } else {
    peerCount.value = Math.max(0, peerCount.value - 1);
  }
}
