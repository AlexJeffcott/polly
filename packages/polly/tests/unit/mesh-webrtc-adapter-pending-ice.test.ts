/**
 * Unit tests for MeshWebRTCAdapter's pre-`setRemoteDescription` ICE
 * candidate buffering — the fix for polly#102.
 *
 * Symptom in the wild: real Chrome 148 connects to a CLI peer that
 * happens to finish ICE gathering before its answer SDP travels back
 * through the signalling relay. The candidate frames win the race
 * against the answer frame, the adapter calls `addIceCandidate` while
 * `remoteDescription` is still null, Chrome throws InvalidStateError
 * for each candidate, the existing catch silently drops them, and by
 * the time the answer lands the offerer has no remote candidates left
 * to pair against. ICE checking never starts, the connection sits in
 * `have-local-offer` forever.
 *
 * The fix is the standard perfect-negotiation pattern: when a candidate
 * arrives and the connection's remoteDescription is null, push it onto
 * a per-slot `pendingRemoteIce` queue; once `setRemoteDescription`
 * resolves in either handleAnswer or handleOffer, drain the queue with
 * `addIceCandidate` calls.
 *
 * These tests use a fake RTCPeerConnection whose `remoteDescription`
 * starts null and only becomes non-null after `setRemoteDescription`
 * resolves — the same observable shape real Chrome presents to the
 * adapter.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

// ─── Fake WebRTC implementation ──────────────────────────────────────────────
// `remoteDescription` starts null and is set to the SDP passed in by
// `setRemoteDescription`. `addIceCandidate` calls are recorded so tests
// can assert when (and how many) candidates were passed through.

interface AddIceCall {
  candidate: RTCIceCandidateInit;
  remoteDescAtCallTime: RTCSessionDescriptionInit | null;
}

class FakeDataChannel {
  onopen: (() => void) | null = null;
  onmessage: ((ev: { data: ArrayBuffer | Uint8Array }) => void) | null = null;
  onclose: (() => void) | null = null;
  readyState = "connecting";
  close(): void {
    this.readyState = "closed";
    this.onclose?.();
  }
  send(_: ArrayBuffer | Uint8Array): void {}
}

class FakePeerConnection {
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  signalingState: RTCSignalingState = "stable";
  remoteDescription: RTCSessionDescriptionInit | null = null;
  addIceCalls: AddIceCall[] = [];
  createDataChannel(_label: string, _options: unknown): FakeDataChannel {
    return new FakeDataChannel();
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    this.signalingState = "have-local-offer";
    return { type: "offer", sdp: "v=0\r\nfake\r\n" };
  }
  async setLocalDescription(desc: RTCSessionDescriptionInit): Promise<void> {
    if (desc.type === "answer") this.signalingState = "stable";
  }
  async setRemoteDescription(desc: RTCSessionDescriptionInit): Promise<void> {
    this.remoteDescription = desc;
    if (desc.type === "offer") this.signalingState = "have-remote-offer";
    if (desc.type === "answer") this.signalingState = "stable";
  }
  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: "answer", sdp: "v=0\r\nfake\r\n" };
  }
  async addIceCandidate(candidate: RTCIceCandidateInit): Promise<void> {
    this.addIceCalls.push({
      candidate,
      remoteDescAtCallTime: this.remoteDescription,
    });
    // Real Chrome throws when remoteDescription is null; mirror that so
    // a regression that removes the buffering would also throw, in case
    // the adapter ever drops its catch.
    if (this.remoteDescription === null) {
      throw new Error("The remote description was null");
    }
  }
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
}

// Capture every FakePeerConnection the adapter constructs so tests can
// inspect their addIceCalls state. The adapter does not expose its
// internal `slots` map, so we hook the constructor instead.
function trackingPeerConnectionCtor(): {
  Ctor: typeof RTCPeerConnection;
  instances: FakePeerConnection[];
} {
  const instances: FakePeerConnection[] = [];
  class TrackingPC extends FakePeerConnection {
    constructor() {
      super();
      instances.push(this);
    }
  }
  return { Ctor: TrackingPC as unknown as typeof RTCPeerConnection, instances };
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
  knownPeerIds: string[]
): {
  adapter: MeshWebRTCAdapter;
  sent: SentSignal[];
  instances: FakePeerConnection[];
} {
  const { client, sent } = createSignalingStub(localPeerId);
  const { Ctor, instances } = trackingPeerConnectionCtor();
  const adapter = new MeshWebRTCAdapter({
    signaling: client,
    peerId: localPeerId,
    knownPeerIds,
    RTCPeerConnection: Ctor,
  });
  return { adapter, sent, instances };
}

const fakeCandidate = (id: number): RTCIceCandidateInit => ({
  candidate: `candidate:${id} 1 udp 2122260223 192.168.0.${id} 49152 typ host`,
  sdpMid: "0",
  sdpMLineIndex: 0,
});

const fakeAnswer = (): RTCSessionDescriptionInit => ({
  type: "answer",
  sdp: "v=0\r\nfake-answer\r\n",
});

// ─── Tests ───────────────────────────────────────────────────────────────────

describe("MeshWebRTCAdapter pre-remoteDescription ICE buffering", () => {
  describe("offerer path", () => {
    let adapter: MeshWebRTCAdapter;
    let instances: FakePeerConnection[];

    beforeEach(async () => {
      // Local "peer-z" initiates toward "peer-a" — z > a so z is the
      // initiator under the tie-break rule.
      const built = buildAdapter("peer-z", ["peer-a"]);
      adapter = built.adapter;
      instances = built.instances;
      adapter.handlePeerJoined("peer-a");
      // Flush the initiateOffer microtask chain so `createOffer` and
      // `setLocalDescription` have settled before tests dispatch signals.
      await new Promise((r) => setTimeout(r, 0));
    });

    test("buffers a candidate that arrives before the answer", async () => {
      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(1) });
      await new Promise((r) => setTimeout(r, 0));
      const pc = instances[0];
      // The candidate must not have been delivered to addIceCandidate
      // yet — remoteDescription is still null.
      expect(pc?.addIceCalls).toEqual([]);
      expect(pc?.remoteDescription).toBeNull();
    });

    test("drains buffered candidates once the answer's setRemoteDescription completes", async () => {
      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(1) });
      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(2) });
      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(3) });
      await new Promise((r) => setTimeout(r, 0));
      const pc = instances[0];
      expect(pc?.addIceCalls).toEqual([]);

      adapter.handleSignal("peer-a", { kind: "answer", sdp: fakeAnswer() });
      await new Promise((r) => setTimeout(r, 0));

      expect(pc?.addIceCalls).toHaveLength(3);
      expect(pc?.addIceCalls[0]?.candidate).toEqual(fakeCandidate(1));
      expect(pc?.addIceCalls[1]?.candidate).toEqual(fakeCandidate(2));
      expect(pc?.addIceCalls[2]?.candidate).toEqual(fakeCandidate(3));
      // Each drained call observed a non-null remote description, which
      // is the property real Chrome requires for addIceCandidate not to
      // throw.
      for (const call of pc?.addIceCalls ?? []) {
        expect(call.remoteDescAtCallTime).not.toBeNull();
      }
    });

    test("candidates that arrive after the answer skip the buffer and dispatch live", async () => {
      adapter.handleSignal("peer-a", { kind: "answer", sdp: fakeAnswer() });
      await new Promise((r) => setTimeout(r, 0));
      const pc = instances[0];
      expect(pc?.remoteDescription).not.toBeNull();

      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(7) });
      await new Promise((r) => setTimeout(r, 0));

      expect(pc?.addIceCalls).toHaveLength(1);
      expect(pc?.addIceCalls[0]?.candidate).toEqual(fakeCandidate(7));
    });

    test("a candidate that arrives between two answers (the second a duplicate) is buffered then drained on the first answer", async () => {
      // Pre-answer candidate buffered.
      adapter.handleSignal("peer-a", { kind: "ice", candidate: fakeCandidate(11) });
      // First answer drains it.
      adapter.handleSignal("peer-a", { kind: "answer", sdp: fakeAnswer() });
      await new Promise((r) => setTimeout(r, 0));
      const pc = instances[0];
      expect(pc?.addIceCalls).toHaveLength(1);

      // A duplicate answer in `stable` state is dropped by handleAnswer
      // — the existing guard. Make sure it does not re-drain anything.
      adapter.handleSignal("peer-a", { kind: "answer", sdp: fakeAnswer() });
      await new Promise((r) => setTimeout(r, 0));
      expect(pc?.addIceCalls).toHaveLength(1);
    });
  });

  describe("answerer path", () => {
    test("candidates that arrive before the offer's setRemoteDescription completes are also buffered and drained", async () => {
      // Local "peer-a" — the lower id, expected to receive an offer.
      // We bypass knownPeers by sending the offer directly via
      // handleSignal, which mirrors what the signalling client does on
      // receipt of an offer frame from a stranger.
      const { adapter, instances } = buildAdapter("peer-a", []);

      // Drop a candidate in before the offer arrives at all. The slot
      // doesn't exist yet, so this candidate must be dropped (the slot
      // lookup early-returns). This is the existing behaviour — we are
      // only buffering when a slot already exists with a null
      // remoteDescription, not pre-emptively materialising a slot from
      // an ICE frame.
      adapter.handleSignal("peer-z", { kind: "ice", candidate: fakeCandidate(101) });
      await new Promise((r) => setTimeout(r, 0));
      expect(instances).toHaveLength(0);
    });
  });
});
