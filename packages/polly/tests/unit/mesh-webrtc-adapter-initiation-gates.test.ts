/**
 * Adapter-level tests for the initiation gate cascade in
 * mesh-webrtc-adapter: evaluateInitiation's named rejection reasons (self /
 * not-in-keyring / not-present / slot-already-exists / tie-break-other-side),
 * the post-construction dial prompts addKnownPeer and refreshKnownPeers, and
 * snapshotInitiationDecision's preference for a sticky fatal-error over a
 * fresh re-evaluation.
 *
 * The gate reasons are read off the public getPeerStateSnapshot() surface —
 * the same `slotInitiationRejectionReason` a consumer logs — so the
 * assertions pin the actual named reason rather than only the slot/no-slot
 * behaviour the peer-discovery suite already covers.
 */

import { describe, expect, test } from "bun:test";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

function createSignalingStub(peerId: string): MeshSignalingClient {
  const options: MeshSignalingClientOptions = {
    url: "ws://stub",
    peerId,
    onSignal: () => {},
  };
  return {
    url: options.url,
    peerId,
    isConnected: true,
    sendSignal: (): boolean => true,
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
}

class FakeDataChannel {
  onopen: (() => void) | null = null;
  onmessage: ((ev: { data: ArrayBuffer | Uint8Array }) => void) | null = null;
  onclose: (() => void) | null = null;
  onerror: ((ev: unknown) => void) | null = null;
  readyState: "connecting" | "open" | "closed" = "connecting";
  close(): void {
    this.readyState = "closed";
    this.onclose?.();
  }
}

class FakePeerConnection {
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  channel?: FakeDataChannel;

  createDataChannel(_label: string, _options: unknown): FakeDataChannel {
    this.channel = new FakeDataChannel();
    return this.channel;
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: "offer", sdp: "v=0\r\nfake\r\n" };
  }
  async setLocalDescription(_d: RTCSessionDescriptionInit): Promise<void> {}
  async setRemoteDescription(_d: RTCSessionDescriptionInit): Promise<void> {}
  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: "answer", sdp: "v=0\r\nfake\r\n" };
  }
  async addIceCandidate(_c: unknown): Promise<void> {}
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
}

function build(localPeerId: string, knownPeerIds: string[]): MeshWebRTCAdapter {
  return new MeshWebRTCAdapter({
    signaling: createSignalingStub(localPeerId),
    peerId: localPeerId,
    knownPeerIds,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
  });
}

/** The named rejection reason getPeerStateSnapshot reports for one peer. */
function reasonFor(adapter: MeshWebRTCAdapter, peerId: string): string | undefined {
  const entry = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === peerId);
  if (!entry) throw new Error(`peer ${peerId} absent from snapshot`);
  return entry.slotInitiationRejectionReason;
}

/** Whether getPeerStateSnapshot reports a live slot for one peer. */
function hasSlot(adapter: MeshWebRTCAdapter, peerId: string): boolean {
  const entry = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === peerId);
  return entry?.slot !== undefined;
}

function presentPeers(adapter: MeshWebRTCAdapter): Set<string> {
  return (adapter as unknown as { presentPeers: Set<string> }).presentPeers;
}

describe("evaluateInitiation named gate reasons", () => {
  test("our own id is rejected as self", () => {
    // The captured-set knownPeerIds path does not filter our own id, so it
    // surfaces in the snapshot where the self gate can be observed.
    const adapter = build("peer-m", ["peer-m"]);
    expect(reasonFor(adapter, "peer-m")).toBe("self");
  });

  test("a present peer that is not in the keyring is rejected as not-in-keyring", () => {
    const adapter = build("peer-z", ["peer-a"]);
    adapter.handlePeersPresent(["stranger"]);
    expect(reasonFor(adapter, "stranger")).toBe("not-in-keyring");
  });

  test("a known peer that has not appeared is rejected as not-present", () => {
    const adapter = build("peer-z", ["peer-a"]);
    expect(reasonFor(adapter, "peer-a")).toBe("not-present");
  });

  test("a peer we already hold a slot for is rejected as slot-already-exists", () => {
    const adapter = build("peer-z", ["peer-a"]);
    adapter.handlePeerJoined("peer-a");
    expect(hasSlot(adapter, "peer-a")).toBe(true);
    expect(reasonFor(adapter, "peer-a")).toBe("slot-already-exists");
  });

  test("a higher-id present peer is deferred as tie-break-other-side", () => {
    // Local id is lexicographically lower, so the remote initiates.
    const adapter = build("peer-a", ["peer-z"]);
    adapter.handlePeerJoined("peer-z");
    expect(hasSlot(adapter, "peer-z")).toBe(false);
    expect(reasonFor(adapter, "peer-z")).toBe("tie-break-other-side");
  });

  test("a known, present, lower-id peer passes every gate (no rejection reason)", () => {
    const adapter = build("peer-z", ["peer-a"]);
    // Roster membership without the dial path, so the gate result is read
    // before a slot turns the decision into slot-already-exists.
    presentPeers(adapter).add("peer-a");
    const entry = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === "peer-a");
    if (!entry) throw new Error("peer-a absent from snapshot");
    expect(entry.slotInitiationRejectionReason).toBeUndefined();
    expect(entry.slotInitiationDecision.decision).toBe("accepted");
    expect(entry.slot).toBeUndefined();
  });

  test("a rejected peer reports a rejected decision alongside its reason", () => {
    const adapter = build("peer-z", ["peer-a"]);
    const entry = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === "peer-a");
    if (!entry) throw new Error("peer-a absent from snapshot");
    expect(entry.slotInitiationDecision.decision).toBe("rejected");
    expect(entry.slotInitiationDecision.reason).toBe("not-present");
  });
});

describe("addKnownPeer post-construction dial prompt", () => {
  test("dials a freshly-known peer that is already present and ours to initiate", () => {
    const adapter = build("peer-z", ["peer-a"]);
    // peer-b shows up before it is in the keyring — rejected as not-in-keyring.
    adapter.handlePeersPresent(["peer-b"]);
    expect(reasonFor(adapter, "peer-b")).toBe("not-in-keyring");
    expect(hasSlot(adapter, "peer-b")).toBe(false);
    // Pairing completes: addKnownPeer registers it and dials immediately.
    adapter.addKnownPeer("peer-b");
    expect(hasSlot(adapter, "peer-b")).toBe(true);
  });

  test("is a no-op for our own id", () => {
    const adapter = build("peer-z", ["peer-a"]);
    adapter.addKnownPeer("peer-z");
    // The self guard returns before the keyring is touched, so our own id
    // is never registered as a dial target.
    expect(adapter.knownPeerIds).not.toContain("peer-z");
    expect(hasSlot(adapter, "peer-z")).toBe(false);
  });

  test("registers a not-yet-present peer without dialling it", () => {
    const adapter = build("peer-z", ["peer-a"]);
    adapter.addKnownPeer("peer-b");
    // Now known, but absent from signalling — no slot, reason not-present.
    expect(adapter.knownPeerIds).toContain("peer-b");
    expect(hasSlot(adapter, "peer-b")).toBe(false);
    expect(reasonFor(adapter, "peer-b")).toBe("not-present");
  });

  test("does not dial a present peer when the tie-break names the other side", () => {
    const adapter = build("peer-a", ["peer-x"]);
    adapter.handlePeersPresent(["peer-z"]);
    adapter.addKnownPeer("peer-z");
    // peer-z is higher, so we wait for its offer rather than dialling.
    expect(hasSlot(adapter, "peer-z")).toBe(false);
    expect(reasonFor(adapter, "peer-z")).toBe("tie-break-other-side");
  });
});

describe("refreshKnownPeers sweep", () => {
  test("dials every present, known, ours-to-initiate peer that has no slot yet", () => {
    const adapter = build("peer-z", ["peer-a", "peer-b"]);
    // Put both peers in the signalling roster without going through the
    // dial path, so the sweep is what opens their slots.
    presentPeers(adapter).add("peer-a");
    presentPeers(adapter).add("peer-b");
    expect(hasSlot(adapter, "peer-a")).toBe(false);
    expect(hasSlot(adapter, "peer-b")).toBe(false);
    adapter.refreshKnownPeers();
    expect(hasSlot(adapter, "peer-a")).toBe(true);
    expect(hasSlot(adapter, "peer-b")).toBe(true);
  });

  test("is idempotent — a second sweep opens no further slots", () => {
    const adapter = build("peer-z", ["peer-a"]);
    presentPeers(adapter).add("peer-a");
    adapter.refreshKnownPeers();
    expect(hasSlot(adapter, "peer-a")).toBe(true);
    const before = adapter.getPeerStateSnapshot().peers.filter((p) => p.slot).length;
    adapter.refreshKnownPeers();
    const after = adapter.getPeerStateSnapshot().peers.filter((p) => p.slot).length;
    expect(after).toBe(before);
  });

  test("does not dial a present higher-id peer", () => {
    const adapter = build("peer-a", ["peer-z"]);
    presentPeers(adapter).add("peer-z");
    adapter.refreshKnownPeers();
    expect(hasSlot(adapter, "peer-z")).toBe(false);
  });
});

describe("tryCreateInitiatingSlot resilience", () => {
  test("records a fatal-error decision when the RTCPeerConnection constructor throws", () => {
    class ThrowingPC {
      constructor() {
        throw new Error("connection cap exceeded");
      }
    }
    const adapter = new MeshWebRTCAdapter({
      signaling: createSignalingStub("peer-z"),
      peerId: "peer-z",
      knownPeerIds: ["peer-a"],
      RTCPeerConnection: ThrowingPC as unknown as typeof RTCPeerConnection,
    });
    // The dial throws inside `new RTCPeerConnection()`; the per-peer
    // try/catch must record it as fatal-error rather than let the throw
    // escape and skip the rest of a batch (polly#106).
    expect(() => adapter.handlePeerJoined("peer-a")).not.toThrow();
    const entry = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === "peer-a");
    if (!entry) throw new Error("peer-a absent from snapshot");
    expect(entry.slotInitiationRejectionReason).toBe("fatal-error");
    expect(entry.slotInitiationDecision.decision).toBe("rejected");
    expect(entry.slotInitiationDecision.error).toBe("connection cap exceeded");
    expect(entry.slot).toBeUndefined();
  });
});

describe("whenReady", () => {
  test("resolves immediately once the adapter is ready", async () => {
    const adapter = build("peer-z", ["peer-a"]);
    (adapter as unknown as { ready: boolean }).ready = true;
    // A ready adapter must hand back an already-resolved promise rather
    // than parking the caller behind the readyResolver.
    let resolved = false;
    void adapter.whenReady().then(() => {
      resolved = true;
    });
    await Promise.resolve();
    expect(resolved).toBe(true);
  });

  test("stays pending until the adapter becomes ready", async () => {
    const adapter = build("peer-z", ["peer-a"]);
    let resolved = false;
    void adapter.whenReady().then(() => {
      resolved = true;
    });
    await Promise.resolve();
    expect(resolved).toBe(false);
  });
});

describe("snapshotInitiationDecision sticky fatal-error", () => {
  type Decision = {
    decision: string;
    reason: string | undefined;
    error: string | undefined;
    at: number;
  };
  function decisionMap(adapter: MeshWebRTCAdapter): Map<string, Decision> {
    return (adapter as unknown as { lastSlotInitiationDecisions: Map<string, Decision> })
      .lastSlotInitiationDecisions;
  }

  test("prefers a cached fatal-error over re-evaluating the gates", () => {
    const adapter = build("peer-z", ["peer-a"]);
    // peer-a would otherwise evaluate to not-present; a sticky fatal-error
    // from a failed construction must win until a sweep clears it.
    decisionMap(adapter).set("peer-a", {
      decision: "rejected",
      reason: "fatal-error",
      error: "boom",
      at: 1,
    });
    expect(reasonFor(adapter, "peer-a")).toBe("fatal-error");
  });

  test("re-evaluates the gates when the cached reason is not fatal-error", () => {
    const adapter = build("peer-z", ["peer-a"]);
    // A stale non-fatal cached reason must not mask the live gate result.
    decisionMap(adapter).set("peer-a", {
      decision: "rejected",
      reason: "self",
      error: undefined,
      at: 1,
    });
    expect(reasonFor(adapter, "peer-a")).toBe("not-present");
  });
});
