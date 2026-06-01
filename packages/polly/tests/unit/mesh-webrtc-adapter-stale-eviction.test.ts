/**
 * Adapter-level tests for the stale-slot keep/evict guards in
 * mesh-webrtc-adapter (evictStaleSlotForRejoin, polly#133). The
 * peer-discovery suite proves the end-to-end rejoin behaviour; this suite
 * pins the individual gate conditions the cascade turns on — the
 * connected+open keep, the young-handshake keep, and the boundary cases
 * (connected-but-channel-not-open, channel-gone, the new/connecting state
 * set, the never-connected deadline, and a zero timeout) that the
 * behavioural tests never exercise.
 *
 * evictStaleSlotForRejoin is driven directly so the keep/evict decision is
 * read synchronously off `slots.has` — without the async re-dial that
 * handlePeerJoined chains on after an eviction.
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

const LOCAL = "peer-z";
const REMOTE = "peer-a";

interface SlotInternals {
  connection: { connectionState: string };
  channel?: { readyState: string };
  createdAt: number;
}

/** Build an adapter with a single initiating slot for REMOTE, then hand the
 * slot back so a test can drive its connection/channel/age into the exact
 * shape one eviction gate turns on. */
function buildWithSlot(slotNeverConnectedTimeoutMs?: number): {
  adapter: MeshWebRTCAdapter;
  slot: SlotInternals;
  evict: () => void;
  hasSlot: () => boolean;
} {
  const adapter = new MeshWebRTCAdapter({
    signaling: createSignalingStub(LOCAL),
    peerId: LOCAL,
    knownPeerIds: [REMOTE],
    slotNeverConnectedTimeoutMs,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
  });
  adapter.handlePeerJoined(REMOTE);
  const slots = (adapter as unknown as { slots: Map<string, SlotInternals> }).slots;
  const slot = slots.get(REMOTE);
  if (!slot) throw new Error("test setup: no slot created");
  return {
    adapter,
    slot,
    evict: () =>
      (adapter as unknown as { evictStaleSlotForRejoin(id: string): void }).evictStaleSlotForRejoin(
        REMOTE
      ),
    hasSlot: () => slots.has(REMOTE),
  };
}

describe("evictStaleSlotForRejoin keep-the-live-slot gate", () => {
  test("keeps a slot that is connected with an open data channel", () => {
    const { slot, evict, hasSlot } = buildWithSlot();
    slot.connection.connectionState = "connected";
    if (slot.channel) slot.channel.readyState = "open";
    evict();
    expect(hasSlot()).toBe(true);
  });

  test("evicts a connected slot whose data channel is not open", () => {
    // Both halves of the guard are required: a connected connection with a
    // still-connecting channel is not a sound, data-carrying slot.
    const { slot, evict, hasSlot } = buildWithSlot();
    slot.connection.connectionState = "connected";
    if (slot.channel) slot.channel.readyState = "connecting";
    evict();
    expect(hasSlot()).toBe(false);
  });

  test("evicts an open-channel slot whose connection is no longer connected", () => {
    const { slot, evict, hasSlot } = buildWithSlot();
    slot.connection.connectionState = "disconnected";
    if (slot.channel) slot.channel.readyState = "open";
    evict();
    expect(hasSlot()).toBe(false);
  });

  test("does not throw, and evicts, when a connected slot has no channel at all", () => {
    // The optional chain on slot.channel guards the no-channel case; a bare
    // member access would throw here instead of falling through to evict.
    const { slot, evict, hasSlot } = buildWithSlot();
    slot.connection.connectionState = "connected";
    slot.channel = undefined;
    expect(() => evict()).not.toThrow();
    expect(hasSlot()).toBe(false);
  });
});

describe("evictStaleSlotForRejoin young-handshake gate", () => {
  test("keeps a brand-new slot still negotiating within the deadline", () => {
    const { slot, evict, hasSlot } = buildWithSlot(30_000);
    slot.connection.connectionState = "new";
    slot.createdAt = performance.now();
    evict();
    expect(hasSlot()).toBe(true);
  });

  test("keeps a connecting slot still within the deadline", () => {
    // Pins the `state === "connecting"` arm of the new/connecting set.
    const { slot, evict, hasSlot } = buildWithSlot(30_000);
    slot.connection.connectionState = "connecting";
    slot.createdAt = performance.now();
    evict();
    expect(hasSlot()).toBe(true);
  });

  test("evicts a new slot that has aged past the never-connected deadline", () => {
    const { slot, evict, hasSlot } = buildWithSlot(5);
    slot.connection.connectionState = "new";
    slot.createdAt = performance.now() - 1_000;
    evict();
    expect(hasSlot()).toBe(false);
  });

  test("evicts a young slot in a state outside the new/connecting set", () => {
    const { slot, evict, hasSlot } = buildWithSlot(30_000);
    slot.connection.connectionState = "disconnected";
    slot.createdAt = performance.now();
    evict();
    expect(hasSlot()).toBe(false);
  });

  test("evicts a young slot when the never-connected deadline is disabled (timeout 0)", () => {
    // timeout 0 means the young-handshake grace period is off entirely, so
    // even a freshly created slot is treated as evictable. Pins the `> 0`.
    const { slot, evict, hasSlot } = buildWithSlot(0);
    slot.connection.connectionState = "new";
    slot.createdAt = performance.now();
    evict();
    expect(hasSlot()).toBe(false);
  });

  // A createdAt far in the future drives `now - createdAt` strongly negative
  // (age below any deadline). performance.now() is only a few ms into a test
  // run, so an ordinary age-0 slot cannot distinguish the age arithmetic from
  // its sign-flipped mutant — the negative age forces the difference.
  const FAR_FUTURE = 1e12;

  test("keeps a slot whose age is negative, pinning the age subtraction", () => {
    const { slot, evict, hasSlot } = buildWithSlot(100);
    slot.connection.connectionState = "new";
    slot.createdAt = FAR_FUTURE;
    // Real: now - FAR_FUTURE is hugely negative, well under the 100ms
    // deadline, so the slot is kept. A `+` in place of `-` makes the value
    // ~FAR_FUTURE, far over the deadline, and would wrongly evict.
    evict();
    expect(hasSlot()).toBe(true);
  });

  test("evicts a negative-age slot when the deadline is disabled, pinning the > 0 gate", () => {
    const { slot, evict, hasSlot } = buildWithSlot(0);
    slot.connection.connectionState = "new";
    slot.createdAt = FAR_FUTURE;
    // With the deadline disabled the slot is evicted despite the negative
    // age. A `>= 0` in place of `> 0` would re-open the grace period and
    // (because the age is now negative) wrongly keep it.
    evict();
    expect(hasSlot()).toBe(false);
  });
});
