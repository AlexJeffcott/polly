/**
 * Unit tests for the polly#109 silent-throw recovery and the
 * polly#109/#110 slot watchdog.
 *
 * Two named wedge shapes the adapter previously could not recover
 * from on its own:
 *
 *   - polly#109: `initiateOffer` was fire-and-forget. A rejection
 *     inside `createOffer` or `setLocalDescription` left the slot
 *     registered with no SDP set, ICE never gathering, and
 *     `connectionState === "new"` indefinitely. The recovery sweep
 *     hit `slot-already-exists` forever and never retried.
 *
 *   - polly#110: a remote process killed without an OS-layer FIN
 *     left the slot at `connectionState === "connected"` while the
 *     data channel sent bytes into the void. ICE keepalives can
 *     take many minutes to fail; without an application-layer
 *     liveness check the slot stayed wedged the whole time.
 *
 * Both are fixed by tearing the wedged slot down so the recovery
 * sweep can re-attempt. The `.catch` on `initiateOffer` handles the
 * fast path; the watchdog handles the broader family (any slot at
 * `new`/`connecting` past the timeout, or any connected slot with
 * no inbound bytes past the timeout).
 */

import { afterEach, describe, expect, test } from "bun:test";
import type { PeerId } from "@automerge/automerge-repo/slim";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

// ─── Fake WebRTC implementation with controllable knobs ──────────────────────

class FakeDataChannel {
  onopen: (() => void) | null = null;
  onmessage: ((ev: { data: ArrayBuffer | Uint8Array }) => void) | null = null;
  onclose: (() => void) | null = null;
  onerror: ((ev: unknown) => void) | null = null;
  readyState = "connecting";
  close(): void {
    this.readyState = "closed";
    this.onclose?.();
  }
  send(_: ArrayBuffer | Uint8Array): void {}
  /** Test helper: flip the channel into the open state. */
  flipOpen(): void {
    this.readyState = "open";
    this.onopen?.();
  }
}

interface FakePeerConnectionOptions {
  /** When set, `createOffer` rejects with this error. Used to reproduce
   * the polly#109 silent-throw shape. */
  failCreateOffer?: Error;
  /** When set, `setLocalDescription` rejects with this error. */
  failSetLocalDescription?: Error;
}

class FakePeerConnection {
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  signalingState = "stable";
  iceConnectionState = "new";
  localDescription: RTCSessionDescriptionInit | null = null;
  remoteDescription: RTCSessionDescriptionInit | null = null;
  channel: FakeDataChannel | undefined;
  static nextOptions: FakePeerConnectionOptions = {};
  private readonly options: FakePeerConnectionOptions;
  constructor() {
    this.options = FakePeerConnection.nextOptions;
    FakePeerConnection.nextOptions = {};
  }
  createDataChannel(_label: string, _opts: unknown): FakeDataChannel {
    this.channel = new FakeDataChannel();
    return this.channel;
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    if (this.options.failCreateOffer) throw this.options.failCreateOffer;
    return { type: "offer", sdp: "v=0\r\nfake\r\n" };
  }
  async setLocalDescription(desc: RTCSessionDescriptionInit): Promise<void> {
    if (this.options.failSetLocalDescription) throw this.options.failSetLocalDescription;
    this.localDescription = desc;
  }
  async setRemoteDescription(desc: RTCSessionDescriptionInit): Promise<void> {
    this.remoteDescription = desc;
  }
  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: "answer", sdp: "v=0\r\nfake\r\n" };
  }
  async addIceCandidate(_candidate: unknown): Promise<void> {}
  async getStats(): Promise<RTCStatsReport> {
    return new Map() as unknown as RTCStatsReport;
  }
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
  /** Test helper: transition into a target `connectionState` and
   * notify listeners. */
  transition(state: string): void {
    this.connectionState = state;
    this.onconnectionstatechange?.();
  }
}

// ─── Signalling client stub ──────────────────────────────────────────────────

interface SentSignal {
  targetPeerId: string;
  payload: unknown;
}

function createSignalingStub(peerId: string): {
  client: MeshSignalingClient;
  sent: SentSignal[];
  options: MeshSignalingClientOptions;
} {
  const sent: SentSignal[] = [];
  const options: MeshSignalingClientOptions = {
    url: "ws://stub",
    peerId,
    onSignal: () => {},
  };
  const client = {
    url: options.url,
    peerId,
    isConnected: true,
    sendSignal(targetPeerId: string, payload: unknown): boolean {
      sent.push({ targetPeerId, payload });
      return true;
    },
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
  return { client, sent, options };
}

// ─── Adapter factory ─────────────────────────────────────────────────────────

interface BuildAdapterOptions {
  slotNeverConnectedTimeoutMs?: number;
  slotIdleTimeoutMs?: number;
  slotWatchdogIntervalMs?: number;
}

function buildAdapter(
  localPeerId: string,
  knownPeerIds: string[],
  opts: BuildAdapterOptions = {}
): { adapter: MeshWebRTCAdapter; sent: SentSignal[] } {
  const { client, sent } = createSignalingStub(localPeerId);
  const adapter = new MeshWebRTCAdapter({
    signaling: client,
    peerId: localPeerId,
    knownPeerIds,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
    slotNeverConnectedTimeoutMs: opts.slotNeverConnectedTimeoutMs,
    slotIdleTimeoutMs: opts.slotIdleTimeoutMs,
    slotWatchdogIntervalMs: opts.slotWatchdogIntervalMs,
  });
  return { adapter, sent };
}

async function flushMicrotasks(): Promise<void> {
  await new Promise((r) => setTimeout(r, 0));
}

// ─── Tests ───────────────────────────────────────────────────────────────────

describe("MeshWebRTCAdapter polly#109 silent-throw recovery", () => {
  afterEach(() => {
    FakePeerConnection.nextOptions = {};
  });

  test("tears down the slot when createOffer rejects, leaving no slot for the recovery sweep", async () => {
    FakePeerConnection.nextOptions = { failCreateOffer: new Error("createOffer boom") };
    const { adapter } = buildAdapter("peer-m", ["peer-a"]);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    await flushMicrotasks();
    expect(adapter.peerSlotCount()).toBe(0);
    const snap = adapter.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-a");
    expect(entry?.slotInitiationDecision.reason).toBe("fatal-error");
    expect(entry?.slotInitiationDecision.error).toContain("createOffer boom");
  });

  test("tears down the slot when setLocalDescription rejects", async () => {
    FakePeerConnection.nextOptions = {
      failSetLocalDescription: new Error("setLocalDescription boom"),
    };
    const { adapter } = buildAdapter("peer-m", ["peer-a"]);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    await flushMicrotasks();
    expect(adapter.peerSlotCount()).toBe(0);
    const snap = adapter.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-a");
    expect(entry?.slotInitiationDecision.reason).toBe("fatal-error");
    expect(entry?.slotInitiationDecision.error).toContain("setLocalDescription boom");
  });

  test("emits peer-disconnected so Automerge stops routing through the dead slot", async () => {
    FakePeerConnection.nextOptions = { failCreateOffer: new Error("boom") };
    const { adapter } = buildAdapter("peer-m", ["peer-a"]);
    const disconnects: string[] = [];
    adapter.on("peer-disconnected", (payload: { peerId: PeerId }) => {
      disconnects.push(payload.peerId as unknown as string);
    });
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    await flushMicrotasks();
    expect(disconnects).toEqual(["peer-a"]);
  });

  test("a subsequent handlePeerJoined after the .catch teardown creates a fresh slot", async () => {
    FakePeerConnection.nextOptions = { failCreateOffer: new Error("boom") };
    const { adapter, sent } = buildAdapter("peer-m", ["peer-a"]);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    await flushMicrotasks();
    expect(adapter.peerSlotCount()).toBe(0);

    // No failure on the retry — the next PC instance picks up the
    // empty options.
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    expect(adapter.peerSlotCount()).toBe(1);
    expect(sent.at(-1)?.targetPeerId).toBe("peer-a");
  });
});

describe("MeshWebRTCAdapter polly#109/#110 slot watchdog", () => {
  test("tears down a slot whose connectionState never advances past 'new' (polly#109 broader family)", async () => {
    const { adapter } = buildAdapter("peer-m", ["peer-a"], {
      slotNeverConnectedTimeoutMs: 10,
      slotIdleTimeoutMs: 0,
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect("peer-m" as unknown as PeerId);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    expect(adapter.peerSlotCount()).toBe(1);

    // Let the watchdog fire past the never-connected timeout. The
    // FakePeerConnection stays at connectionState='new' indefinitely.
    await new Promise((r) => setTimeout(r, 50));
    expect(adapter.peerSlotCount()).toBe(0);
    const snap = adapter.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-a");
    expect(entry?.slotInitiationDecision.reason).toBe("fatal-error");
    expect(entry?.slotInitiationDecision.error).toContain("never reached connected");

    adapter.disconnect();
  });

  test("tears down a 'connected'-looking slot with no inbound bytes after the idle timeout (polly#110)", async () => {
    const { adapter } = buildAdapter("peer-m", ["peer-a"], {
      slotNeverConnectedTimeoutMs: 0,
      slotIdleTimeoutMs: 20,
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect("peer-m" as unknown as PeerId);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    const slotEntries = [...((adapter as unknown as { slots: Map<string, unknown> }).slots ?? [])];
    const slot = slotEntries[0]?.[1] as unknown as {
      connection: FakePeerConnection;
      channel: FakeDataChannel | undefined;
    };
    expect(slot).toBeDefined();
    slot.connection.transition("connected");
    slot.channel?.flipOpen();

    await new Promise((r) => setTimeout(r, 60));
    expect(adapter.peerSlotCount()).toBe(0);
    const snap = adapter.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-a");
    expect(entry?.slotInitiationDecision.reason).toBe("fatal-error");
    expect(entry?.slotInitiationDecision.error).toContain("idle");

    adapter.disconnect();
  });

  test("keeps a connected slot alive while inbound bytes are still arriving", async () => {
    const { adapter } = buildAdapter("peer-m", ["peer-a"], {
      slotNeverConnectedTimeoutMs: 0,
      slotIdleTimeoutMs: 50,
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect("peer-m" as unknown as PeerId);
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    const slot = (
      adapter as unknown as {
        slots: Map<
          string,
          { connection: FakePeerConnection; channel: FakeDataChannel | undefined }
        >;
      }
    ).slots.get("peer-a");
    expect(slot).toBeDefined();
    if (!slot) return;
    slot.connection.transition("connected");
    slot.channel?.flipOpen();

    // Drip inbound frames in every 10ms for 80ms — well past the
    // 50ms idle timeout. The watchdog should NOT tear the slot
    // down because lastInboundAt keeps advancing.
    const interval = setInterval(() => {
      slot.channel?.onmessage?.({ data: new Uint8Array([1, 2, 3]) });
    }, 10);
    await new Promise((r) => setTimeout(r, 80));
    clearInterval(interval);
    expect(adapter.peerSlotCount()).toBe(1);

    adapter.disconnect();
  });

  test("snapshot exposes createdAt and lastInboundAt for each slot", async () => {
    const { adapter } = buildAdapter("peer-m", ["peer-a"], {
      slotWatchdogIntervalMs: 0,
    });
    adapter.handlePeerJoined("peer-a");
    await flushMicrotasks();
    const snap = adapter.getPeerStateSnapshot();
    const entry = snap.peers.find((p) => p.peerId === "peer-a");
    expect(entry?.slot?.createdAt).toBeDefined();
    expect(entry?.slot?.createdAt).toBeGreaterThan(0);
    expect(entry?.slot?.lastInboundAt).toBeUndefined();
  });

  test("disconnect stops the watchdog timer", async () => {
    const { adapter } = buildAdapter("peer-m", ["peer-a"], {
      slotNeverConnectedTimeoutMs: 5,
      slotWatchdogIntervalMs: 2,
    });
    adapter.connect("peer-m" as unknown as PeerId);
    adapter.disconnect();
    // If the watchdog were still running, this delay would let it
    // fire and any throw would surface as an unhandled rejection.
    await new Promise((r) => setTimeout(r, 20));
    expect(adapter.peerSlotCount()).toBe(0);
  });
});
