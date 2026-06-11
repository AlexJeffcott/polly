/**
 * Unit tests for MeshWebRTCAdapter timer lifecycle and watchdog disable
 * boundaries.
 *
 * Mutation testing (polly#161) left the periodic-sweep and watchdog guard
 * conditions as covered-but-undetected theatre: the existing watchdog suite
 * drives the *teardown* paths (timeout > 0, slot wedges, gets torn down) but
 * never the *disable* / *lifecycle* boundaries — a sweep that should not start
 * because the interval is 0 or no keyringSource was supplied, a watchdog gate
 * disabled by a 0 timeout, the timers stopping on disconnect. Those guards
 * (`knownPeersRefreshIntervalMs <= 0`, `keyringSource === undefined`,
 * `slotNeverConnectedTimeoutMs > 0`, `slotIdleTimeoutMs > 0 && connected`)
 * survived every mutation. These tests pin the boundaries.
 */
import { afterEach, describe, expect, test } from "bun:test";
import type { PeerMetadata, StorageId } from "@automerge/automerge-repo/slim";
import type { MeshKeyring } from "@/shared/lib/mesh-network-adapter";
import type { MeshSignalingClient } from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";
import { generateSigningKeyPair } from "@/shared/lib/signing";
import { peerId } from "./helpers/branded";

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
  flipOpen(): void {
    this.readyState = "open";
    this.onopen?.();
  }
}

class FakePeerConnection {
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  channel: FakeDataChannel | undefined;
  createDataChannel(_label: string, _opts: unknown): FakeDataChannel {
    this.channel = new FakeDataChannel();
    return this.channel;
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: "offer", sdp: "v=0\r\nfake\r\n" };
  }
  async setLocalDescription(_desc: RTCSessionDescriptionInit): Promise<void> {}
  async setRemoteDescription(_desc: RTCSessionDescriptionInit): Promise<void> {}
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
  transition(state: string): void {
    this.connectionState = state;
    this.onconnectionstatechange?.();
  }
}

function signalingStub(peerId: string): MeshSignalingClient {
  return {
    url: "ws://stub",
    peerId,
    isConnected: true,
    sendSignal: () => true,
    connect: async () => {},
    close: () => {},
  } as unknown as MeshSignalingClient;
}

function keyring(peers: string[] = []): MeshKeyring {
  return {
    identity: generateSigningKeyPair(),
    knownPeers: new Map(peers.map((p) => [p, generateSigningKeyPair().publicKey])),
    documentKeys: new Map(),
    revokedPeers: new Set(),
  };
}

interface BuildOpts {
  knownPeerIds?: string[];
  keyringSource?: () => MeshKeyring;
  knownPeersRefreshIntervalMs?: number;
  slotNeverConnectedTimeoutMs?: number;
  slotIdleTimeoutMs?: number;
  slotWatchdogIntervalMs?: number;
}

const adapters: MeshWebRTCAdapter[] = [];

function build(localPeerId: string, opts: BuildOpts = {}): MeshWebRTCAdapter {
  const adapter = new MeshWebRTCAdapter({
    signaling: signalingStub(localPeerId),
    peerId: localPeerId,
    knownPeerIds: opts.knownPeerIds ?? [],
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
    ...(opts.keyringSource && { keyringSource: opts.keyringSource }),
    ...(opts.knownPeersRefreshIntervalMs !== undefined && {
      knownPeersRefreshIntervalMs: opts.knownPeersRefreshIntervalMs,
    }),
    ...(opts.slotNeverConnectedTimeoutMs !== undefined && {
      slotNeverConnectedTimeoutMs: opts.slotNeverConnectedTimeoutMs,
    }),
    ...(opts.slotIdleTimeoutMs !== undefined && { slotIdleTimeoutMs: opts.slotIdleTimeoutMs }),
    ...(opts.slotWatchdogIntervalMs !== undefined && {
      slotWatchdogIntervalMs: opts.slotWatchdogIntervalMs,
    }),
  });
  adapters.push(adapter);
  return adapter;
}

const sleep = (ms: number): Promise<void> => new Promise((r) => setTimeout(r, ms));
const flush = (): Promise<void> => sleep(0);

afterEach(() => {
  for (const a of adapters) a.disconnect();
  adapters.length = 0;
});

// ─── known-peers sweep lifecycle ────────────────────────────────────────────────

describe("MeshWebRTCAdapter known-peers sweep lifecycle", () => {
  test("starts the sweep on connect when a keyringSource and a positive interval are set", () => {
    const adapter = build("peer-m", {
      keyringSource: () => keyring(),
      knownPeersRefreshIntervalMs: 50,
    });
    expect(adapter.getPeerStateSnapshot().sweep.enabled).toBe(false);
    adapter.connect(peerId("peer-m"));
    const sweep = adapter.getPeerStateSnapshot().sweep;
    expect(sweep.enabled).toBe(true);
    expect(sweep.intervalMs).toBe(50);
  });

  test("does not start the sweep when the interval is 0", () => {
    const adapter = build("peer-m", {
      keyringSource: () => keyring(),
      knownPeersRefreshIntervalMs: 0,
    });
    adapter.connect(peerId("peer-m"));
    expect(adapter.getPeerStateSnapshot().sweep.enabled).toBe(false);
  });

  test("does not start the sweep when no keyringSource is supplied", () => {
    const adapter = build("peer-m", { knownPeersRefreshIntervalMs: 50 });
    adapter.connect(peerId("peer-m"));
    expect(adapter.getPeerStateSnapshot().sweep.enabled).toBe(false);
  });

  test("disconnect stops the sweep timer", () => {
    const adapter = build("peer-m", {
      keyringSource: () => keyring(),
      knownPeersRefreshIntervalMs: 50,
    });
    adapter.connect(peerId("peer-m"));
    expect(adapter.getPeerStateSnapshot().sweep.enabled).toBe(true);
    adapter.disconnect();
    expect(adapter.getPeerStateSnapshot().sweep.enabled).toBe(false);
  });

  test("the sweep actually ticks: runCount advances and lastRunAt is stamped", async () => {
    const adapter = build("peer-m", {
      keyringSource: () => keyring(),
      knownPeersRefreshIntervalMs: 10,
    });
    adapter.connect(peerId("peer-m"));
    expect(adapter.getPeerStateSnapshot().sweep.runCount).toBe(0);
    await sleep(35);
    const sweep = adapter.getPeerStateSnapshot().sweep;
    expect(sweep.runCount).toBeGreaterThanOrEqual(1);
    expect(sweep.lastRunAt).toBeDefined();
  });
});

// ─── watchdog disable boundaries ────────────────────────────────────────────────

describe("MeshWebRTCAdapter watchdog disable boundaries", () => {
  test("a 0 never-connected timeout disables the never-connected teardown", async () => {
    const adapter = build("peer-z", {
      knownPeerIds: ["peer-a"],
      slotNeverConnectedTimeoutMs: 0, // disabled
      slotIdleTimeoutMs: 0,
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect(peerId("peer-z"));
    adapter.handlePeerJoined("peer-a"); // "peer-z" > "peer-a" → we initiate
    await flush();
    expect(adapter.peerSlotCount()).toBe(1);
    // The slot stays at connectionState 'new' forever; with the timeout
    // disabled the watchdog must NOT reap it.
    await sleep(40);
    expect(adapter.peerSlotCount()).toBe(1);
  });

  test("a 0 idle timeout disables the idle teardown for a connected slot", async () => {
    const adapter = build("peer-z", {
      knownPeerIds: ["peer-a"],
      slotNeverConnectedTimeoutMs: 0,
      slotIdleTimeoutMs: 0, // disabled
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect(peerId("peer-z"));
    adapter.handlePeerJoined("peer-a");
    await flush();
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
    // No inbound bytes, but the idle timeout is disabled, so the slot
    // survives indefinitely.
    await sleep(40);
    expect(adapter.peerSlotCount()).toBe(1);
  });

  test("a 0 watchdog interval disables the watchdog entirely", async () => {
    const adapter = build("peer-z", {
      knownPeerIds: ["peer-a"],
      slotNeverConnectedTimeoutMs: 5, // would reap a wedged slot...
      slotIdleTimeoutMs: 0,
      slotWatchdogIntervalMs: 0, // ...but the watchdog never runs
    });
    adapter.connect(peerId("peer-z"));
    adapter.handlePeerJoined("peer-a");
    await flush();
    expect(adapter.peerSlotCount()).toBe(1);
    // The slot is wedged at 'new' well past the never-connected timeout, but
    // with no watchdog timer it is never inspected, so it stays.
    await sleep(40);
    expect(adapter.peerSlotCount()).toBe(1);
  });

  test("a long never-connected timeout leaves a young slot untouched", async () => {
    const adapter = build("peer-z", {
      knownPeerIds: ["peer-a"],
      slotNeverConnectedTimeoutMs: 10_000, // far in the future
      slotIdleTimeoutMs: 0,
      slotWatchdogIntervalMs: 5,
    });
    adapter.connect(peerId("peer-z"));
    adapter.handlePeerJoined("peer-a");
    await flush();
    // The watchdog runs repeatedly but the slot's age stays well under the
    // timeout, so it must not be torn down.
    await sleep(30);
    expect(adapter.peerSlotCount()).toBe(1);
  });
});

// ─── connect peer-metadata ──────────────────────────────────────────────────────

describe("MeshWebRTCAdapter connect peer-metadata", () => {
  test("stores peer metadata when supplied on connect", () => {
    const adapter = build("peer-m");
    // StorageId is a branded string with no runtime constructor.
    const meta: PeerMetadata = {
      storageId: "store-1" as unknown as StorageId,
      isEphemeral: false,
    };
    adapter.connect(peerId("peer-m"), meta);
    expect((adapter as unknown as { peerMetadata?: unknown }).peerMetadata).toEqual(meta);
  });

  test("leaves peer metadata unset when omitted on connect", () => {
    const adapter = build("peer-m");
    adapter.connect(peerId("peer-m"));
    expect((adapter as unknown as { peerMetadata?: unknown }).peerMetadata).toBeUndefined();
  });
});
