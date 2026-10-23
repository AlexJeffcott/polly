/**
 * Complete `MeshWebRTCAdapter.getPeerStateSnapshot()` peer entries for tests
 * that drive the mesh-client snapshot enrichment directly. Every field has a
 * neutral default, so a test states only the peer id and the per-handle wire
 * data it asserts on. Replaces partial doubles cast to the snapshot type.
 */
import type { HandleSyncSnapshot, MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

/** One entry of `getPeerStateSnapshot().peers`. */
export type AdapterPeerSnapshot = ReturnType<
  MeshWebRTCAdapter["getPeerStateSnapshot"]
>["peers"][number];

/** The `slot` view of a peer that has an RTC slot. */
export type AdapterSlotSnapshot = NonNullable<AdapterPeerSnapshot["slot"]>;

/** A connected, idle slot carrying the given per-document wire data. */
export function adapterSlot(handles: Record<string, HandleSyncSnapshot>): AdapterSlotSnapshot {
  return {
    signalingState: "stable",
    iceConnectionState: "connected",
    connectionState: "connected",
    dataChannelState: "open",
    pendingSendCount: 0,
    pendingRemoteIceCount: 0,
    inFlightSync: undefined,
    transport: undefined,
    lastSyncHandshakeAttempt: {
      dataChannelOpenedAt: undefined,
      peerCandidateEmittedAt: undefined,
      firstOutboundSendAt: undefined,
      firstInboundMessageAt: undefined,
    },
    handles,
    createdAt: 0,
    lastInboundAt: undefined,
  };
}

/** A known, present peer whose slot initiation was accepted. Pass
 *  `undefined` for a peer the adapter holds no slot for. */
export function adapterPeer(
  peerId: string,
  slot: AdapterSlotSnapshot | undefined
): AdapterPeerSnapshot {
  return {
    peerId,
    knownInKeyring: true,
    presentInSignalling: true,
    slotInitiationRejectionReason: undefined,
    slotInitiationDecision: {
      decision: "accepted",
      reason: undefined,
      error: undefined,
      at: 0,
    },
    slot,
  };
}
