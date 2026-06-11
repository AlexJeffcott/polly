/**
 * Adapter-level tests for the polly#105 relay-enforcement island and the
 * {@link MeshWebRTCAdapter.handleSignal} dispatch.
 *
 * When `iceTransportPolicy: "relay"` is set with `iceRelayEnforcement` on,
 * polly must filter non-relay ICE candidates out of *both* the trickle
 * stream it emits and the SDP descriptions it forwards — Chrome filters at
 * the source but werift still advertises host/srflx candidates upstream, so
 * a relay-only peer can otherwise pair against a non-relay candidate. These
 * tests pin every branch of that filter (the typed `candidate.type` path,
 * the legacy `typ X` SDP-string path, the policy/enforcement guards) plus
 * the signal-dispatch routing and the receive-side candidate buffering.
 *
 * The adapter is wired against a hand-rolled fake RTCPeerConnection so the
 * test sits on top of bun:test with no real WebRTC.
 */

import { beforeEach, describe, expect, test } from "bun:test";
import type {
  MeshSignalingClient,
  MeshSignalingClientOptions,
} from "@/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

type SentSignal = { target: string; payload: { kind: string; [k: string]: unknown } };

/** A signalling stub that records every sendSignal call so a test can
 * assert what (if anything) the adapter forwarded to the relay. */
function createCapturingSignaling(peerId: string): {
  signaling: MeshSignalingClient;
  sent: SentSignal[];
} {
  const sent: SentSignal[] = [];
  const options: MeshSignalingClientOptions = {
    url: "ws://stub",
    peerId,
    onSignal: () => {},
  };
  const signaling = {
    url: options.url,
    peerId,
    isConnected: true,
    sendSignal(target: string, payload: SentSignal["payload"]): boolean {
      sent.push({ target, payload });
      return true;
    },
    connect: async (): Promise<void> => {},
    close: (): void => {},
  } as unknown as MeshSignalingClient;
  return { signaling, sent };
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

/** A fake RTCPeerConnection rich enough to drive the offer/answer/ICE
 * paths: it captures the constructor config, lets a test fire
 * onicecandidate, records addIceCandidate calls, and exposes settable
 * remoteDescription/signalingState so the buffering and glare branches
 * are reachable. createOffer/createAnswer return SDP with a configurable
 * candidate block so the SDP filter has something to strip. */
class FakePeerConnection {
  static instances: FakePeerConnection[] = [];
  static offerSdp = "v=0\r\nfake\r\n";
  static answerSdp = "v=0\r\nfake\r\n";

  config: RTCConfiguration;
  onicecandidate: ((ev: { candidate: unknown }) => void) | null = null;
  onconnectionstatechange: (() => void) | null = null;
  ondatachannel: ((ev: { channel: FakeDataChannel }) => void) | null = null;
  connectionState = "new";
  signalingState: RTCSignalingState = "have-local-offer";
  remoteDescription: RTCSessionDescriptionInit | null = null;
  localDescription: RTCSessionDescriptionInit | null = null;
  channel?: FakeDataChannel;
  addedIce: RTCIceCandidateInit[] = [];

  constructor(config?: RTCConfiguration) {
    this.config = config ?? {};
    FakePeerConnection.instances.push(this);
  }

  createDataChannel(_label: string, _options: unknown): FakeDataChannel {
    this.channel = new FakeDataChannel();
    return this.channel;
  }
  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: "offer", sdp: FakePeerConnection.offerSdp };
  }
  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: "answer", sdp: FakePeerConnection.answerSdp };
  }
  async setLocalDescription(d: RTCSessionDescriptionInit): Promise<void> {
    // A real RTCPeerConnection canonicalises the SDP and exposes the
    // finalised form via `localDescription` — that finalised description,
    // not the raw create*() return, is what the adapter must forward. The
    // FINALISED: marker lets a test prove the adapter reads localDescription.
    this.localDescription = { type: d.type, sdp: `FINALISED:${d.sdp ?? ""}` };
  }
  async setRemoteDescription(d: RTCSessionDescriptionInit): Promise<void> {
    this.remoteDescription = d;
  }
  async addIceCandidate(c: RTCIceCandidateInit): Promise<void> {
    this.addedIce.push(c);
  }
  close(): void {
    this.connectionState = "closed";
    this.onconnectionstatechange?.();
  }
}

function makeAdapter(
  overrides: Partial<{
    iceTransportPolicy: RTCIceTransportPolicy;
    iceRelayEnforcement: boolean;
    iceServers: RTCIceServer[];
    localPeerId: string;
    knownPeerIds: string[];
  }> = {}
): { adapter: MeshWebRTCAdapter; sent: SentSignal[] } {
  const localPeerId = overrides.localPeerId ?? "peer-z";
  const { signaling, sent } = createCapturingSignaling(localPeerId);
  const adapter = new MeshWebRTCAdapter({
    signaling,
    peerId: localPeerId,
    knownPeerIds: overrides.knownPeerIds ?? ["peer-a"],
    iceTransportPolicy: overrides.iceTransportPolicy,
    iceRelayEnforcement: overrides.iceRelayEnforcement,
    iceServers: overrides.iceServers,
    RTCPeerConnection: FakePeerConnection as unknown as typeof RTCPeerConnection,
  });
  return { adapter, sent };
}

/** Resolve after pending microtasks + one macrotask so the async
 * fire-and-forget initiateOffer/handleOffer chains settle. */
const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

function iceCandidate(opts: { candidate: string; type?: string }): RTCIceCandidate {
  return {
    candidate: opts.candidate,
    type: opts.type,
    toJSON(): RTCIceCandidateInit {
      return { candidate: opts.candidate };
    },
  } as unknown as RTCIceCandidate;
}

/** Pull the sdp string out of a captured signal payload, narrowing the
 * untyped `[k: string]: unknown` field instead of casting. */
function payloadSdp(payload: SentSignal["payload"]): string {
  const sdp = payload.sdp;
  if (typeof sdp === "object" && sdp !== null && "sdp" in sdp && typeof sdp.sdp === "string") {
    return sdp.sdp;
  }
  return "";
}

const RELAY_LINE = "a=candidate:1 1 udp 100 10.0.0.1 9 typ relay";
const HOST_LINE = "a=candidate:2 1 udp 200 192.168.1.2 9 typ host";
const SRFLX_LINE = "a=candidate:3 1 udp 150 1.2.3.4 9 typ srflx";

beforeEach(() => {
  FakePeerConnection.instances = [];
  FakePeerConnection.offerSdp = "v=0\r\nfake\r\n";
  FakePeerConnection.answerSdp = "v=0\r\nfake\r\n";
});

describe("MeshWebRTCAdapter buildRtcConfiguration", () => {
  test("relay policy and ice servers reach the RTCPeerConnection config", () => {
    const iceServers = [{ urls: "turn:turn.example:3478" }];
    const { adapter } = makeAdapter({ iceTransportPolicy: "relay", iceServers });
    adapter.handlePeerJoined("peer-a");
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no peer connection built");
    expect(pc.config.iceTransportPolicy).toBe("relay");
    expect(pc.config.iceServers).toEqual(iceServers);
  });

  test("omits iceTransportPolicy entirely when none is configured", () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: undefined });
    adapter.handlePeerJoined("peer-a");
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no peer connection built");
    expect("iceTransportPolicy" in pc.config).toBe(false);
  });
});

describe("MeshWebRTCAdapter trickle-ICE relay filter (shouldSendCandidate)", () => {
  function fireCandidate(adapter: MeshWebRTCAdapter, candidate: RTCIceCandidate | null): void {
    adapter.handlePeerJoined("peer-a");
    const pc = FakePeerConnection.instances[0];
    if (!pc?.onicecandidate) throw new Error("onicecandidate not wired");
    pc.onicecandidate({ candidate });
  }

  test("forwards a relay candidate identified by its typed field", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    fireCandidate(adapter, iceCandidate({ candidate: HOST_LINE, type: "relay" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(1);
  });

  test("forwards a relay candidate identified by the legacy SDP string", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    fireCandidate(adapter, iceCandidate({ candidate: "x typ relay y" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(1);
  });

  test("drops a non-relay candidate under relay policy", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    fireCandidate(adapter, iceCandidate({ candidate: "x typ host y", type: "host" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(0);
  });

  test("drops a candidate whose type cannot be determined", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    fireCandidate(adapter, iceCandidate({ candidate: "no typ token here" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(0);
  });

  test("forwards every candidate when enforcement is disabled", () => {
    const { adapter, sent } = makeAdapter({
      iceTransportPolicy: "relay",
      iceRelayEnforcement: false,
    });
    fireCandidate(adapter, iceCandidate({ candidate: "x typ host y", type: "host" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(1);
  });

  test("forwards every candidate when the policy is not relay", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "all" });
    fireCandidate(adapter, iceCandidate({ candidate: "x typ host y", type: "host" }));
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(1);
  });

  test("ignores an end-of-candidates event with a null candidate", () => {
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    fireCandidate(adapter, null);
    expect(sent.filter((s) => s.payload.kind === "ice")).toHaveLength(0);
  });
});

describe("MeshWebRTCAdapter SDP candidate filtering", () => {
  test("strips non-relay candidate lines from the outgoing offer SDP", async () => {
    FakePeerConnection.offerSdp = [
      "v=0",
      "m=application 9 UDP/DTLS/SCTP webrtc-datachannel",
      RELAY_LINE,
      HOST_LINE,
      SRFLX_LINE,
    ].join("\r\n");
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "relay" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const offer = sent.find((s) => s.payload.kind === "offer");
    if (!offer) throw new Error("no offer sent");
    const sdp = payloadSdp(offer.payload);
    expect(sdp).toContain(RELAY_LINE);
    expect(sdp).not.toContain(HOST_LINE);
    expect(sdp).not.toContain(SRFLX_LINE);
    // Non-candidate lines are preserved verbatim.
    expect(sdp).toContain("m=application 9 UDP/DTLS/SCTP webrtc-datachannel");
  });

  test("leaves the offer SDP untouched when policy is not relay", async () => {
    FakePeerConnection.offerSdp = ["v=0", RELAY_LINE, HOST_LINE].join("\r\n");
    const { adapter, sent } = makeAdapter({ iceTransportPolicy: "all" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const offer = sent.find((s) => s.payload.kind === "offer");
    if (!offer) throw new Error("no offer sent");
    const sdp = payloadSdp(offer.payload);
    expect(sdp).toContain(HOST_LINE);
  });

  test("leaves the offer SDP untouched when enforcement is disabled", async () => {
    FakePeerConnection.offerSdp = ["v=0", RELAY_LINE, HOST_LINE].join("\r\n");
    const { adapter, sent } = makeAdapter({
      iceTransportPolicy: "relay",
      iceRelayEnforcement: false,
    });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const offer = sent.find((s) => s.payload.kind === "offer");
    if (!offer) throw new Error("no offer sent");
    const sdp = payloadSdp(offer.payload);
    expect(sdp).toContain(HOST_LINE);
  });

  test("filters the answer SDP it sends back for an incoming offer", async () => {
    FakePeerConnection.answerSdp = ["v=0", RELAY_LINE, HOST_LINE].join("\r\n");
    // Local id "peer-a" < incoming "peer-b" so the glare rule accepts the offer.
    const { adapter, sent } = makeAdapter({
      iceTransportPolicy: "relay",
      localPeerId: "peer-a",
    });
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    const answer = sent.find((s) => s.payload.kind === "answer");
    if (!answer) throw new Error("no answer sent");
    const sdp = payloadSdp(answer.payload);
    expect(sdp).toContain(RELAY_LINE);
    expect(sdp).not.toContain(HOST_LINE);
  });

  test("sends the finalised localDescription, not the raw createAnswer SDP", async () => {
    FakePeerConnection.answerSdp = "v=0\r\nraw-answer\r\n";
    const { adapter, sent } = makeAdapter({
      iceTransportPolicy: "all",
      localPeerId: "peer-a",
    });
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    const answer = sent.find((s) => s.payload.kind === "answer");
    if (!answer) throw new Error("no answer sent");
    const sdp = payloadSdp(answer.payload);
    expect(sdp).toContain("FINALISED:");
  });

  test("filters the incoming offer SDP before applying it as the remote description", async () => {
    const { adapter } = makeAdapter({
      iceTransportPolicy: "relay",
      localPeerId: "peer-a",
    });
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: ["v=0", RELAY_LINE, HOST_LINE].join("\r\n") },
    });
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc?.remoteDescription) throw new Error("remote description never set");
    expect(pc.remoteDescription.sdp).toContain(RELAY_LINE);
    expect(pc.remoteDescription.sdp).not.toContain(HOST_LINE);
  });
});

describe("MeshWebRTCAdapter handleSignal dispatch", () => {
  test("a payload that is not an object is a no-op", () => {
    const { adapter, sent } = makeAdapter({ localPeerId: "peer-a" });
    adapter.handleSignal("peer-b", "not-an-object");
    adapter.handleSignal("peer-b", null);
    adapter.handleSignal("peer-b", { sdp: "missing kind" });
    expect(sent).toHaveLength(0);
    expect(FakePeerConnection.instances).toHaveLength(0);
  });

  test("an offer builds an answerer slot and replies with an answer", async () => {
    const { adapter, sent } = makeAdapter({ localPeerId: "peer-a" });
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    expect(sent.some((s) => s.payload.kind === "answer")).toBe(true);
    expect(FakePeerConnection.instances).toHaveLength(1);
  });

  test("an answer for a pending local offer applies the remote description", async () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: "all" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no slot");
    pc.signalingState = "have-local-offer";
    pc.remoteDescription = null;
    adapter.handleSignal("peer-a", {
      kind: "answer",
      sdp: { type: "answer", sdp: "v=0\r\nanswer\r\n" },
    });
    await flush();
    expect(pc.remoteDescription).not.toBeNull();
  });

  test("an answer for an unknown peer is a no-op that resolves cleanly", async () => {
    const { adapter } = makeAdapter({ localPeerId: "peer-a" });
    // No slot exists for this peer; handleAnswer must bail before touching
    // slot.connection rather than throwing on the undefined slot.
    await expect(
      (
        adapter as unknown as {
          handleAnswer(id: string, sdp: RTCSessionDescriptionInit): Promise<void>;
        }
      ).handleAnswer("ghost-peer", { type: "answer", sdp: "v=0\r\n" })
    ).resolves.toBeUndefined();
  });

  test("an answer that arrives outside the have-local-offer state is dropped", async () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: "all" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no slot");
    pc.signalingState = "stable";
    pc.remoteDescription = null;
    adapter.handleSignal("peer-a", {
      kind: "answer",
      sdp: { type: "answer", sdp: "v=0\r\nanswer\r\n" },
    });
    await flush();
    expect(pc.remoteDescription).toBeNull();
  });
});

describe("MeshWebRTCAdapter incoming ICE candidates", () => {
  test("drops a non-relay incoming candidate under relay policy", async () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: "relay" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no slot");
    pc.remoteDescription = { type: "answer", sdp: "v=0\r\n" };
    adapter.handleSignal("peer-a", {
      kind: "ice",
      candidate: { candidate: "x typ host y" } satisfies RTCIceCandidateInit,
    });
    await flush();
    expect(pc.addedIce).toHaveLength(0);
  });

  test("applies a relay incoming candidate once the remote description is set", async () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: "relay" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no slot");
    pc.remoteDescription = { type: "answer", sdp: "v=0\r\n" };
    adapter.handleSignal("peer-a", {
      kind: "ice",
      candidate: { candidate: "x typ relay y" } satisfies RTCIceCandidateInit,
    });
    await flush();
    expect(pc.addedIce).toHaveLength(1);
  });

  test("buffers a candidate that arrives before the remote description, then drains it", async () => {
    const { adapter } = makeAdapter({ iceTransportPolicy: "all" });
    adapter.handlePeerJoined("peer-a");
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc) throw new Error("no slot");
    pc.remoteDescription = null;
    adapter.handleSignal("peer-a", {
      kind: "ice",
      candidate: { candidate: "x typ host y" } satisfies RTCIceCandidateInit,
    });
    await flush();
    // Buffered, not applied yet.
    expect(pc.addedIce).toHaveLength(0);
    // An answer sets the remote description and drains the buffer.
    pc.signalingState = "have-local-offer";
    adapter.handleSignal("peer-a", {
      kind: "answer",
      sdp: { type: "answer", sdp: "v=0\r\nanswer\r\n" },
    });
    await flush();
    expect(pc.addedIce).toHaveLength(1);
  });
});

describe("MeshWebRTCAdapter glare resolution", () => {
  // The glare branch keys off `this.peerId` — the repo peer id `connect()`
  // installs, not the construction-time `localPeerId`. In production
  // `connect()` always runs before any signal arrives; setting the field
  // directly mirrors that precondition without starting the sweep/watchdog
  // timers `connect()` would otherwise leak into the test.
  test("the higher local id ignores an incoming offer for an existing slot", async () => {
    const { adapter, sent } = makeAdapter({ localPeerId: "peer-z" });
    (adapter as unknown as { peerId: string }).peerId = "peer-z";
    adapter.handlePeerJoined("peer-a");
    await flush();
    const before = FakePeerConnection.instances.length;
    adapter.handleSignal("peer-a", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    // No new slot built and no answer sent — our own offer stands.
    expect(FakePeerConnection.instances).toHaveLength(before);
    expect(sent.some((s) => s.payload.kind === "answer")).toBe(false);
  });

  test("the lower local id tears down its slot and answers the incoming offer", async () => {
    const { adapter, sent } = makeAdapter({ localPeerId: "peer-a" });
    (adapter as unknown as { peerId: string }).peerId = "peer-a";
    // The lower id never initiates on its own (the tie-break gate yields to
    // the higher peer), so seed the pre-existing slot the glare branch
    // resolves against via the real initiating path.
    (adapter as unknown as { createInitiatingSlot(id: string): unknown }).createInitiatingSlot(
      "peer-b"
    );
    await flush();
    const first = FakePeerConnection.instances[0];
    if (!first) throw new Error("no initiating slot");
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    // The original initiating connection was closed and a fresh answerer built.
    expect(first.connectionState).toBe("closed");
    expect(sent.some((s) => s.payload.kind === "answer")).toBe(true);
  });

  test("resolves the glare when the existing slot is an answerer with no channel yet", async () => {
    // An answerer slot has `channel: undefined` until its ondatachannel
    // fires. A second offer must tear it down without dereferencing the
    // absent channel — guarding the optional-chaining on existing.channel.
    const { adapter } = makeAdapter({ localPeerId: "peer-a" });
    (adapter as unknown as { peerId: string }).peerId = "peer-a";
    const handleOffer = (
      adapter as unknown as {
        handleOffer(id: string, sdp: RTCSessionDescriptionInit): Promise<void>;
      }
    ).handleOffer.bind(adapter);
    await handleOffer("peer-b", { type: "offer", sdp: "v=0\r\nfirst\r\n" });
    const firstAnswerer = FakePeerConnection.instances[0];
    if (!firstAnswerer) throw new Error("no answerer slot");
    expect(firstAnswerer.channel).toBeUndefined();
    // Second offer: existing answerer (no channel) must be torn down cleanly.
    await expect(
      handleOffer("peer-b", { type: "offer", sdp: "v=0\r\nsecond\r\n" })
    ).resolves.toBeUndefined();
    expect(firstAnswerer.connectionState).toBe("closed");
    expect(FakePeerConnection.instances).toHaveLength(2);
  });

  test("wires the data channel an incoming offer's ondatachannel delivers", async () => {
    const { adapter } = makeAdapter({ localPeerId: "peer-a" });
    adapter.handleSignal("peer-b", {
      kind: "offer",
      sdp: { type: "offer", sdp: "v=0\r\nremote\r\n" },
    });
    await flush();
    const pc = FakePeerConnection.instances[0];
    if (!pc?.ondatachannel) throw new Error("ondatachannel not wired");
    const delivered = new FakeDataChannel();
    pc.ondatachannel({ channel: delivered });
    // wireDataChannel installs the channel lifecycle handlers; a wired
    // channel has its onopen set, an unwired one does not.
    expect(delivered.onopen).not.toBeNull();
  });
});
