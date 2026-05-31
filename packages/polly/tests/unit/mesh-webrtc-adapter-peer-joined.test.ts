/**
 * Unit tests for MeshWebRTCAdapter's peer-discovery dispatch.
 *
 * The adapter gains three new public methods that the signalling client
 * will call on `peers-present`, `peer-joined`, and `peer-left` frames:
 *
 *   - handlePeerJoined(peerId): consider a single newly-announced peer.
 *   - handlePeersPresent(peerIds): consider a list of already-joined peers.
 *   - handlePeerLeft(peerId): tear down any slot for a peer that left.
 *
 * The first two must apply the same filter: only initiate an SDP offer
 * when (a) the peer is in `knownPeerIds`, (b) no slot already exists for
 * it, and (c) the tie-break rule — `this.peerId > remotePeerId` under
 * string comparison — designates this side as the initiator.
 *
 * The tie-break direction matches the existing glare-resolution logic
 * in `handleOffer`: the lexicographically higher peer id is the one
 * whose initiator survives any race. Extending the same rule to the
 * pre-offer decision eliminates the glare entirely for the common case
 * where both sides learn of each other at roughly the same time.
 *
 * handlePeerLeft is the counterpart: when a peer disconnects from the
 * signalling server, its entry in our slot map is evicted so that a
 * subsequent rejoin (which fires peer-joined again) creates a fresh
 * slot against the reincarnated peer.
 *
 * These tests stub the signalling client and the RTC peer connection,
 * so they run in plain bun:test with no browser.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

// ─── Fake WebRTC implementation ──────────────────────────────────────────────
// Enough surface for createInitiatingSlot → initiateOffer to run to the
// point of calling signaling.sendSignal with the offer, then stop. No
// actual SDP negotiation happens.

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
  // Every FakePeerConnection registers itself here so a test can reach
  // the connection the adapter built for a peer and drive its
  // `connectionState` — the polly#133 stale-slot tests need to put a
  // slot into a dead or fully-live shape after construction.
  static instances: FakePeerConnection[] = [];
  static reset(): void {
    FakePeerConnection.instances = [];
  }
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  /** The data channel handed back from {@link createDataChannel} on an
   * initiating slot, exposed so a test can flip its `readyState`. */
  lastDataChannel: FakeDataChannel | undefined;
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
  close(): void {
    this.connectionState = "closed";
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

function buildAdapter(
  localPeerId: string,
  knownPeerIds: string[],
  overrides: { slotNeverConnectedTimeoutMs?: number } = {}
): { adapter: MeshWebRTCAdapter; sent: SentSignal[] } {
  FakePeerConnection.reset();
  const { client, sent } = createSignalingStub(localPeerId);
  const adapter = new MeshWebRTCAdapter({
    signaling: client,
    peerId: localPeerId,
    knownPeerIds,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
    ...overrides,
  });
  return { adapter, sent };
}

// ─── Tests ───────────────────────────────────────────────────────────────────

describe("MeshWebRTCAdapter peer-discovery dispatch", () => {
  // Tie-break rule: the lexicographically higher peer id is the initiator.
  // "peer-b" > "peer-a", so "peer-b" initiates toward "peer-a".

  describe("handlePeerJoined", () => {
    let adapter: MeshWebRTCAdapter;
    let sent: SentSignal[];

    beforeEach(() => {
      const built = buildAdapter("peer-b", ["peer-a"]);
      adapter = built.adapter;
      sent = built.sent;
    });

    test("initiates an offer when the remote peer is known and we are the higher id", async () => {
      adapter.handlePeerJoined("peer-a");
      // initiateOffer runs an async chain; flush microtasks.
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toHaveLength(1);
      expect(sent[0]?.targetPeerId).toBe("peer-a");
      const payload = sent[0]?.payload as unknown as { kind?: string };
      expect(payload.kind).toBe("offer");
    });

    test("is a no-op when we are the lower id (remote will initiate toward us)", async () => {
      const { adapter: lowerAdapter, sent: lowerSent } = buildAdapter("peer-a", ["peer-b"]);
      lowerAdapter.handlePeerJoined("peer-b");
      await new Promise((r) => setTimeout(r, 0));
      expect(lowerSent).toEqual([]);
    });

    test("is a no-op when the peer is not in knownPeerIds", async () => {
      adapter.handlePeerJoined("peer-c");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toEqual([]);
    });

    test("is a no-op when a slot for that peer already exists", async () => {
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toHaveLength(1);

      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toHaveLength(1);
    });

    test("is a no-op when the announced peer is our own id", async () => {
      adapter.handlePeerJoined("peer-b");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toEqual([]);
    });
  });

  describe("handlePeersPresent", () => {
    test("fans out to each known peer where we are the higher id", async () => {
      // Local "peer-m" against three knownPeers: one lower, one higher, one unknown.
      const { adapter, sent } = buildAdapter("peer-m", ["peer-a", "peer-z", "peer-stranger"]);
      adapter.handlePeersPresent(["peer-a", "peer-z", "peer-unpaired"]);
      await new Promise((r) => setTimeout(r, 0));
      // Only "peer-a" qualifies: it's in knownPeers and we (peer-m) are higher.
      // "peer-z" is higher than us, so it would initiate toward us.
      // "peer-unpaired" is not in knownPeers.
      expect(sent).toHaveLength(1);
      expect(sent[0]?.targetPeerId).toBe("peer-a");
    });

    test("is a no-op for an empty list", async () => {
      const { adapter, sent } = buildAdapter("peer-m", ["peer-a"]);
      adapter.handlePeersPresent([]);
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toEqual([]);
    });

    test("does not duplicate when a slot is already present for one of the peers", async () => {
      const { adapter, sent } = buildAdapter("peer-m", ["peer-a", "peer-b"]);
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toHaveLength(1);

      adapter.handlePeersPresent(["peer-a", "peer-b"]);
      await new Promise((r) => setTimeout(r, 0));
      // peer-a is already slotted → skipped; peer-b initiates.
      expect(sent).toHaveLength(2);
      expect(sent[1]?.targetPeerId).toBe("peer-b");
    });
  });

  describe("handlePeerLeft", () => {
    test("evicts the slot for a known peer that has left", async () => {
      const { adapter } = buildAdapter("peer-m", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(adapter.peerSlotCount()).toBe(1);

      adapter.handlePeerLeft("peer-a");
      expect(adapter.peerSlotCount()).toBe(0);
    });

    test("is a no-op for a peer that was never slotted", () => {
      const { adapter } = buildAdapter("peer-m", ["peer-a"]);
      adapter.handlePeerLeft("peer-stranger");
      expect(adapter.peerSlotCount()).toBe(0);
    });

    test("a subsequent handlePeerJoined after handlePeerLeft creates a fresh slot", async () => {
      const { adapter, sent } = buildAdapter("peer-m", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(sent).toHaveLength(1);

      adapter.handlePeerLeft("peer-a");
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      // A second offer fires because the slot was evicted in between.
      expect(sent).toHaveLength(2);
      expect(sent[1]?.targetPeerId).toBe("peer-a");
    });
  });

  describe("peerSlotCount helper", () => {
    test("reports the current number of initiating slots", async () => {
      const { adapter } = buildAdapter("peer-m", ["peer-a", "peer-b"]);
      expect(adapter.peerSlotCount()).toBe(0);
      adapter.handlePeerJoined("peer-a");
      await new Promise((r) => setTimeout(r, 0));
      expect(adapter.peerSlotCount()).toBe(1);
      adapter.handlePeerJoined("peer-b");
      await new Promise((r) => setTimeout(r, 0));
      expect(adapter.peerSlotCount()).toBe(2);
    });
  });

  // ─── Polly issue #133 ──────────────────────────────────────────────────────
  // A peer that reuses its peerId across short-lived sessions (a CLI
  // `chat send` re-run from the same keyring is the canonical case)
  // rejoins the signalling server under the same id. Before the fix, a
  // slot left over from the peer's previous session wedged
  // rediscovery: `evaluateInitiation`'s `slot-already-exists` gate
  // refused the re-dial, so the survivor never reconnected until the
  // idle watchdog reaped the corpse minutes later. handlePeerJoined /
  // handlePeersPresent now treat the discovery frame as authoritative
  // proof of a fresh signalling presence and evict a stale slot.
  describe("stale-slot eviction on peer rejoin (polly#133)", () => {
    const flush = () => new Promise((r) => setTimeout(r, 0));

    test("evicts a dead slot and re-dials when the peer rejoins", async () => {
      // peer-b > peer-a, so peer-b is the initiator toward peer-a.
      const { adapter, sent } = buildAdapter("peer-b", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(1);
      expect(adapter.peerSlotCount()).toBe(1);

      // The peer's process exited; its connection died but the slot was
      // never cleaned up (no `peer-left` reached us). Drive the fake
      // connection into a terminal state to model the corpse.
      const connection = FakePeerConnection.instances[0];
      expect(connection).toBeDefined();
      if (connection) connection.connectionState = "failed";

      let disconnected = 0;
      adapter.on("peer-disconnected", () => {
        disconnected += 1;
      });

      // The same peerId rejoins the signalling roster.
      adapter.handlePeerJoined("peer-a");
      await flush();

      // The stale slot was torn down (one peer-disconnected emit) and a
      // fresh offer fired against the reincarnated peer.
      expect(disconnected).toBe(1);
      expect(sent).toHaveLength(2);
      expect(sent[1]?.targetPeerId).toBe("peer-a");
      expect(adapter.peerSlotCount()).toBe(1);
    });

    test("keeps a live slot whose channel survived the peer's signalling reconnect", async () => {
      const { adapter, sent } = buildAdapter("peer-b", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(1);

      // The slot is fully established — connection `connected`, data
      // channel `open`. A `peer-joined` here means the peer reconnected
      // its signalling socket but kept the direct WebRTC session.
      const connection = FakePeerConnection.instances[0];
      expect(connection).toBeDefined();
      if (connection) {
        connection.connectionState = "connected";
        if (connection.lastDataChannel) connection.lastDataChannel.readyState = "open";
      }

      adapter.handlePeerJoined("peer-a");
      await flush();

      // The healthy slot is left intact — no teardown, no re-dial.
      expect(sent).toHaveLength(1);
      expect(adapter.peerSlotCount()).toBe(1);
    });

    test("leaves a young in-flight handshake alone on a duplicate frame", async () => {
      // Default slotNeverConnectedTimeoutMs (30s): a slot created
      // moments ago is still negotiating and must not be restarted.
      const { adapter, sent } = buildAdapter("peer-b", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await flush();
      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(1);
      expect(adapter.peerSlotCount()).toBe(1);
    });

    test("evicts a slot stuck negotiating past the never-connected deadline", async () => {
      // Tiny deadline so a slot that never leaves `new` counts as stale
      // by the time the peer's next discovery frame arrives.
      const { adapter, sent } = buildAdapter("peer-b", ["peer-a"], {
        slotNeverConnectedTimeoutMs: 1,
      });
      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(1);

      // Let the slot age past the 1ms deadline while still at `new`.
      await new Promise((r) => setTimeout(r, 10));

      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(2);
      expect(adapter.peerSlotCount()).toBe(1);
    });

    test("handlePeersPresent also evicts a stale slot on a signalling reconnect", async () => {
      const { adapter, sent } = buildAdapter("peer-b", ["peer-a"]);
      adapter.handlePeerJoined("peer-a");
      await flush();
      expect(sent).toHaveLength(1);

      const connection = FakePeerConnection.instances[0];
      if (connection) connection.connectionState = "failed";

      // A reconnected signalling client receives a fresh peers-present.
      adapter.handlePeersPresent(["peer-a"]);
      await flush();
      expect(sent).toHaveLength(2);
      expect(adapter.peerSlotCount()).toBe(1);
    });
  });
});

describe("MeshWebRTCAdapter connection-state changes (wireConnection)", () => {
  // Drive the RTCPeerConnection.onconnectionstatechange handler the adapter
  // wires up, which mutation testing showed was executed but barely asserted.
  const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

  async function joinedSlot(): Promise<{
    adapter: MeshWebRTCAdapter;
    events: Array<[string, string]>;
    connection: FakePeerConnection;
  }> {
    const { adapter } = buildAdapter("peer-b", ["peer-a"]);
    const events: Array<[string, string]> = [];
    adapter.on("peer-candidate", (e: { peerId: unknown }) =>
      events.push(["candidate", e.peerId as string])
    );
    adapter.on("peer-disconnected", (e: { peerId: unknown }) =>
      events.push(["disconnected", e.peerId as string])
    );
    adapter.handlePeerJoined("peer-a");
    await flush();
    const connection = FakePeerConnection.instances[0];
    if (!connection) throw new Error("expected a connection to have been built");
    return { adapter, events, connection };
  }

  test("emits peer-candidate when the connection reaches 'connected'", async () => {
    const { events, connection } = await joinedSlot();
    connection.connectionState = "connected";
    connection.onconnectionstatechange?.();
    expect(events).toContainEqual(["candidate", "peer-a"]);
  });

  test("emits peer-candidate at most once across repeated 'connected' events", async () => {
    const { events, connection } = await joinedSlot();
    connection.connectionState = "connected";
    connection.onconnectionstatechange?.();
    connection.onconnectionstatechange?.();
    expect(events.filter(([kind]) => kind === "candidate")).toHaveLength(1);
  });

  test("a non-terminal state change emits nothing and keeps the slot", async () => {
    const { adapter, events, connection } = await joinedSlot();
    connection.connectionState = "connecting";
    connection.onconnectionstatechange?.();
    expect(events).toEqual([]);
    expect(adapter.peerSlotCount()).toBe(1);
  });

  for (const terminal of ["disconnected", "failed", "closed"] as const) {
    test(`evicts the slot and emits peer-disconnected on '${terminal}'`, async () => {
      const { adapter, events, connection } = await joinedSlot();
      connection.connectionState = terminal;
      connection.onconnectionstatechange?.();
      expect(events).toContainEqual(["disconnected", "peer-a"]);
      expect(adapter.peerSlotCount()).toBe(0);
    });
  }

  test("does not emit peer-disconnected twice when teardown re-enters the handler", async () => {
    const { events, connection } = await joinedSlot();
    connection.connectionState = "failed";
    connection.onconnectionstatechange?.();
    connection.connectionState = "closed";
    connection.onconnectionstatechange?.();
    expect(events.filter(([kind]) => kind === "disconnected")).toHaveLength(1);
  });
});
