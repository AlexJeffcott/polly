/**
 * Unit tests for MeshWebRTCAdapter's transport-stats parsing layer.
 *
 * `collectTransportSnapshot` and its helpers (`partitionStats`,
 * `ingestStat`/`ingestTransport`/`ingestDataChannel`, `selectActivePair`,
 * `buildCandidatePairView`) turn a raw `RTCStatsReport` into the
 * `TransportSnapshot` the `getPeerStateSnapshot` surface exposes. They are
 * module-private but reachable through `refreshTransportStats(peerId)` /
 * `refreshAllTransportStats()`, and `serialiseSlotView` through
 * `getPeerStateSnapshot()`.
 *
 * These were a NoCoverage island under polly#124 — no test executed them at
 * all. The parsing is pure data-shaping over a crafted stats report, so it
 * runs in plain bun:test against a fake `getStats()` with no browser and no
 * real ICE.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

// ─── Fakes ───────────────────────────────────────────────────────────────────
// Enough surface for createInitiatingSlot to build a slot, plus a settable
// getStats so each test feeds the parser a crafted report.

type Stat = Record<string, unknown>;

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
}

class FakePeerConnection {
  static instances: FakePeerConnection[] = [];
  static reset(): void {
    FakePeerConnection.instances = [];
  }
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  signalingState = "stable";
  iceConnectionState = "new";
  connectionState = "new";
  lastDataChannel: FakeDataChannel | undefined;
  /** Report handed back from getStats; settable per test. */
  nextStats: RTCStatsReport = makeReport([]);
  /** When true, getStats rejects (mirrors a connection mid-teardown). */
  statsThrows = false;
  constructor() {
    FakePeerConnection.instances.push(this);
  }
  createDataChannel(_label: string, _options: unknown): FakeDataChannel {
    const channel = new FakeDataChannel();
    this.lastDataChannel = channel;
    return channel;
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
    if (this.statsThrows) throw new Error("connection closed");
    return this.nextStats;
  }
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
}

/** A Map satisfies the `report.values()` access partitionStats makes, and
 * matches the Map-like shape of a real RTCStatsReport. */
function makeReport(stats: Stat[]): RTCStatsReport {
  return new Map(stats.map((s) => [String(s["id"]), s])) as unknown as RTCStatsReport;
}

function createSignalingStub(peerId: string): MeshSignalingClient {
  const options: MeshSignalingClientOptions = { url: "ws://stub", peerId, onSignal: () => {} };
  return {
    url: options.url,
    peerId,
    isConnected: true,
    sendSignal: (): boolean => true,
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
}

function buildAdapter(localPeerId: string, knownPeerIds: string[]): MeshWebRTCAdapter {
  FakePeerConnection.reset();
  return new MeshWebRTCAdapter({
    signaling: createSignalingStub(localPeerId),
    peerId: localPeerId,
    knownPeerIds,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
  });
}

const flush = (): Promise<void> => new Promise((r) => setTimeout(r, 0));

/** Build a slot toward `remotePeerId` (we are "peer-z", the higher id, so we
 * initiate) and return the FakePeerConnection backing it. */
async function buildSlot(remotePeerId: string): Promise<{
  adapter: MeshWebRTCAdapter;
  conn: FakePeerConnection;
}> {
  const adapter = buildAdapter("peer-z", [remotePeerId]);
  adapter.handlePeerJoined(remotePeerId);
  await flush();
  const conn = FakePeerConnection.instances.at(-1);
  if (!conn) throw new Error("no connection was created for the slot");
  return { adapter, conn };
}

// ─── Tests ───────────────────────────────────────────────────────────────────

describe("MeshWebRTCAdapter transport-stats parsing (polly#124)", () => {
  beforeEach(() => {
    FakePeerConnection.reset();
  });

  test("builds the selected candidate-pair view from a full stats report", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      {
        id: "T1",
        type: "transport",
        selectedCandidatePairId: "P1",
        retransmittedPacketsSent: 3,
        retransmittedBytesSent: 480,
      },
      {
        id: "P1",
        type: "candidate-pair",
        localCandidateId: "L1",
        remoteCandidateId: "R1",
        state: "succeeded",
        nominated: true,
        bytesSent: 1000,
        bytesReceived: 2000,
      },
      { id: "L1", type: "local-candidate", candidateType: "host" },
      { id: "R1", type: "remote-candidate", candidateType: "srflx" },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.retransmittedPacketsSent).toBe(3);
    expect(snap?.retransmittedBytesSent).toBe(480);
    expect(snap?.selectedCandidatePair).toEqual({
      localCandidateType: "host",
      remoteCandidateType: "srflx",
      state: "succeeded",
      nominated: true,
      bytesSent: 1000,
      bytesReceived: 2000,
    });
  });

  test("falls back to the nominated pair when no transport selectedCandidatePairId", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      { id: "T1", type: "transport" }, // no selectedCandidatePairId
      { id: "P1", type: "candidate-pair", nominated: false, localCandidateId: "L1" },
      {
        id: "P2",
        type: "candidate-pair",
        nominated: true,
        localCandidateId: "L2",
        remoteCandidateId: "R2",
        state: "in-progress",
      },
      { id: "L2", type: "local-candidate", candidateType: "relay" },
      { id: "R2", type: "remote-candidate", candidateType: "prflx" },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.selectedCandidatePair?.localCandidateType).toBe("relay");
    expect(snap?.selectedCandidatePair?.remoteCandidateType).toBe("prflx");
    expect(snap?.selectedCandidatePair?.state).toBe("in-progress");
    expect(snap?.selectedCandidatePair?.nominated).toBe(true);
  });

  test("reads retransmit counters off the data-channel when the transport omits them", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      { id: "T1", type: "transport", selectedCandidatePairId: "P1" }, // no retransmit fields
      { id: "D1", type: "data-channel", retransmittedPacketsSent: 7, retransmittedBytesSent: 999 },
      { id: "P1", type: "candidate-pair", nominated: true },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.retransmittedPacketsSent).toBe(7);
    expect(snap?.retransmittedBytesSent).toBe(999);
  });

  test("ignores a data-channel retransmit field that is not a number", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // transport omits retransmit; the data-channel carries non-numeric junk,
    // which the `typeof === "number"` guard must reject rather than adopt.
    conn.nextStats = makeReport([
      { id: "T1", type: "transport", selectedCandidatePairId: "P1" },
      {
        id: "D1",
        type: "data-channel",
        retransmittedPacketsSent: "x",
        retransmittedBytesSent: null,
      },
      { id: "P1", type: "candidate-pair", nominated: true },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.retransmittedPacketsSent).toBeUndefined();
    expect(snap?.retransmittedBytesSent).toBeUndefined();
  });

  test("ignores a transport retransmit field that is not a number", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // The transport itself can carry non-numeric junk in these fields; the
    // `typeof === "number"` guard on the transport path must reject it too.
    conn.nextStats = makeReport([
      {
        id: "T1",
        type: "transport",
        selectedCandidatePairId: "P1",
        retransmittedPacketsSent: "x",
        retransmittedBytesSent: false,
      },
      { id: "P1", type: "candidate-pair", nominated: true },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.retransmittedPacketsSent).toBeUndefined();
    expect(snap?.retransmittedBytesSent).toBeUndefined();
  });

  test("a report with no values() method yields an empty snapshot", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // A bare object (no Map-like `values()`) must short-circuit to an empty
    // parse rather than throw — the `report.values?.() ?? []` fallback.
    conn.nextStats = {} as unknown as RTCStatsReport;

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.selectedCandidatePair).toBeUndefined();
    expect(snap?.retransmittedPacketsSent).toBeUndefined();
  });

  test("falls back to the nominated pair when selectedCandidatePairId names a missing pair", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // The transport points at a pair id that is absent from the report; the
    // lookup misses, so selection must continue to the nominated pair rather
    // than give up.
    conn.nextStats = makeReport([
      { id: "T1", type: "transport", selectedCandidatePairId: "P-missing" },
      { id: "P2", type: "candidate-pair", nominated: true, bytesSent: 77 },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.selectedCandidatePair).toBeDefined();
    expect(snap?.selectedCandidatePair?.bytesSent).toBe(77);
  });

  test("the transport's retransmit counters win over the data-channel's", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // transport listed first, so its counters are ingested before the
    // data-channel's fallback can apply.
    conn.nextStats = makeReport([
      {
        id: "T1",
        type: "transport",
        selectedCandidatePairId: "P1",
        retransmittedPacketsSent: 3,
        retransmittedBytesSent: 480,
      },
      { id: "D1", type: "data-channel", retransmittedPacketsSent: 7, retransmittedBytesSent: 999 },
      { id: "P1", type: "candidate-pair", nominated: true },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.retransmittedPacketsSent).toBe(3);
    expect(snap?.retransmittedBytesSent).toBe(480);
  });

  test("uses '?'/default fields when the selected pair references missing candidates", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      { id: "T1", type: "transport", selectedCandidatePairId: "P1" },
      // pair references candidates that are absent from the report, and omits
      // state/nominated/bytes entirely.
      { id: "P1", type: "candidate-pair", localCandidateId: "gone", remoteCandidateId: "gone" },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.selectedCandidatePair).toEqual({
      localCandidateType: "?",
      remoteCandidateType: "?",
      state: "",
      nominated: false,
      bytesSent: 0,
      bytesReceived: 0,
    });
  });

  test("no selected and no nominated pair yields an undefined candidate-pair view", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      { id: "T1", type: "transport" },
      { id: "P1", type: "candidate-pair", nominated: false },
    ]);

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap?.selectedCandidatePair).toBeUndefined();
  });

  test("a getStats rejection yields an empty snapshot rather than throwing", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.statsThrows = true;

    const snap = await adapter.refreshTransportStats("peer-a");

    expect(snap).toBeDefined();
    expect(snap?.selectedCandidatePair).toBeUndefined();
    expect(snap?.retransmittedPacketsSent).toBeUndefined();
    expect(snap?.retransmittedBytesSent).toBeUndefined();
  });

  test("refreshTransportStats returns undefined for a peer with no slot", async () => {
    const adapter = buildAdapter("peer-z", ["peer-a"]);
    expect(await adapter.refreshTransportStats("peer-a")).toBeUndefined();
  });

  test("refreshAllTransportStats returns one snapshot per active slot", async () => {
    const adapter = buildAdapter("peer-z", ["peer-a", "peer-b"]);
    adapter.handlePeerJoined("peer-a");
    adapter.handlePeerJoined("peer-b");
    await flush();
    for (const conn of FakePeerConnection.instances) {
      conn.nextStats = makeReport([
        { id: "T1", type: "transport", selectedCandidatePairId: "P1" },
        { id: "P1", type: "candidate-pair", nominated: true, bytesSent: 5 },
      ]);
    }

    const all = await adapter.refreshAllTransportStats();

    expect(new Set(all.keys())).toEqual(new Set(["peer-a", "peer-b"]));
    expect(all.get("peer-a")?.selectedCandidatePair?.bytesSent).toBe(5);
  });

  test("getPeerStateSnapshot serialises a slot's view including its transport", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    conn.nextStats = makeReport([
      { id: "T1", type: "transport", selectedCandidatePairId: "P1" },
      { id: "P1", type: "candidate-pair", nominated: true, bytesReceived: 42 },
    ]);
    await adapter.refreshTransportStats("peer-a");

    const snapshot = adapter.getPeerStateSnapshot();
    const peer = snapshot.peers.find((p) => p.peerId === "peer-a");

    expect(peer?.slot).toBeDefined();
    expect(peer?.slot?.connectionState).toBe("new");
    expect(peer?.slot?.dataChannelState).toBe("connecting");
    expect(peer?.slot?.pendingSendCount).toBe(0);
    expect(peer?.slot?.pendingRemoteIceCount).toBe(0);
    expect(peer?.slot?.handles).toEqual({});
    expect(peer?.slot?.transport?.selectedCandidatePair?.bytesReceived).toBe(42);
    expect(peer?.slot?.lastSyncHandshakeAttempt).toEqual({
      dataChannelOpenedAt: undefined,
      peerCandidateEmittedAt: undefined,
      firstOutboundSendAt: undefined,
      firstInboundMessageAt: undefined,
    });
    expect(typeof peer?.slot?.createdAt).toBe("number");
  });

  test("serialises a populated handshake attempt once the data channel opens", async () => {
    const { adapter, conn } = await buildSlot("peer-a");
    // Opening the data channel stamps dataChannelOpenedAt on the slot's
    // handshake attempt, so the serialised view must carry it through (not a
    // blank object).
    conn.lastDataChannel?.onopen?.();

    const peer = adapter.getPeerStateSnapshot().peers.find((p) => p.peerId === "peer-a");

    expect(typeof peer?.slot?.lastSyncHandshakeAttempt.dataChannelOpenedAt).toBe("number");
  });
});
