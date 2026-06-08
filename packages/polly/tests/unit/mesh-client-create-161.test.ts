/**
 * Unit tests for createMeshClient — the one-call factory that wires a
 * signalling client, a WebRTC network adapter, a sign+encrypt
 * MeshNetworkAdapter, and an Automerge Repo into a single MeshClient.
 *
 * Mutation testing (polly#124 Phase 3, re-measured under polly#161) surfaced
 * the factory body at ~0% kill / 231 NoCoverage: every other mesh-client unit
 * test exercises the extracted helpers (the `__test__` exports, the snapshot
 * enrichment, the revocation core) but nothing executed `createMeshClient`
 * itself — it hard-builds a signalling WebSocket and RTCPeerConnections, so it
 * was left to the integration suite, which sits outside the mutation kill-path.
 *
 * The factory is fully injectable, though: `signaling.WebSocket` and
 * `rtc.RTCPeerConnection` are constructor overrides. These tests drive the
 * whole factory off-network with an auto-opening fake WebSocket and a fake
 * RTCPeerConnection, covering option defaulting, the keyring-source shapes,
 * the returned MeshClient surface, and the revocation / connected-peer
 * lifecycle wired onto the network adapter.
 */
import { afterEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId } from "@automerge/automerge-repo/slim";
import { generateDocumentKey } from "@/shared/lib/encryption";
import {
  type CreateMeshClientOptions,
  createMeshClient,
  type MeshClient,
} from "@/shared/lib/mesh-client";
import { type MeshDiagnostic, subscribeToMeshDiagnostics } from "@/shared/lib/mesh-diagnostics";
import {
  DEFAULT_MESH_KEY_ID,
  MESH_CONTROL_TYPE,
  type MeshControlType,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "@/shared/lib/mesh-network-adapter";
import { createRevocation, encodeRevocation } from "@/shared/lib/revocation";
import { encodeRevocationSummary } from "@/shared/lib/revocation-summary";
import { generateSigningKeyPair, type SigningKeyPair } from "@/shared/lib/signing";

// ─── Fakes ───────────────────────────────────────────────────────────────────

/** A WebSocket double that opens itself on the next microtask — after the
 * signalling client has attached its "open" listener inside connect(), so the
 * `await signaling.connect()` inside createMeshClient resolves with no socket. */
class FakeWebSocket {
  static readonly CONNECTING = 0;
  static readonly OPEN = 1;
  static readonly CLOSING = 2;
  static readonly CLOSED = 3;
  static instances: FakeWebSocket[] = [];
  static reset(): void {
    FakeWebSocket.instances = [];
  }
  static last(): FakeWebSocket {
    const ws = FakeWebSocket.instances.at(-1);
    if (!ws) throw new Error("no FakeWebSocket constructed");
    return ws;
  }
  readonly url: string;
  readyState = 0;
  readonly sent: string[] = [];
  closeCalls = 0;
  private readonly listeners = new Map<string, Array<(ev: unknown) => void>>();
  constructor(url: string) {
    this.url = url;
    FakeWebSocket.instances.push(this);
    queueMicrotask(() => {
      this.readyState = 1;
      this.emit("open", {});
    });
  }
  addEventListener(type: string, fn: (ev: unknown) => void): void {
    const list = this.listeners.get(type) ?? [];
    list.push(fn);
    this.listeners.set(type, list);
  }
  send(data: string): void {
    this.sent.push(data);
  }
  close(): void {
    this.closeCalls += 1;
    this.readyState = 3;
    this.emit("close", {});
  }
  emit(type: string, ev: unknown): void {
    for (const fn of this.listeners.get(type) ?? []) fn(ev);
  }
  /** Deliver a signalling frame as the server would. */
  fireMessage(frame: unknown): void {
    this.emit("message", { data: JSON.stringify(frame) });
  }
}
const FakeWS = FakeWebSocket as unknown as typeof WebSocket;

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
  connectionState = "new";
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
const FakePC = FakePeerConnection as unknown as typeof RTCPeerConnection;

const LOCAL = "local-peer";

function makeKeyring(over: Partial<MeshKeyring> = {}): MeshKeyring {
  return {
    identity: generateSigningKeyPair(),
    knownPeers: new Map(),
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, generateDocumentKey()]]),
    revokedPeers: new Set(),
    ...over,
  };
}

const clients: MeshClient[] = [];

interface MakeOverrides {
  signaling?: Partial<CreateMeshClientOptions["signaling"]>;
  rtc?: Partial<NonNullable<CreateMeshClientOptions["rtc"]>>;
  keyring?: CreateMeshClientOptions["keyring"];
  encryptionEnabled?: boolean;
  repoStorage?: CreateMeshClientOptions["repoStorage"];
}

async function make(over: MakeOverrides = {}): Promise<MeshClient> {
  const options: CreateMeshClientOptions = {
    signaling: { url: "ws://localhost:9/sig", peerId: LOCAL, WebSocket: FakeWS, ...over.signaling },
    rtc: { RTCPeerConnection: FakePC, ...over.rtc },
    keyring: over.keyring ?? makeKeyring(),
    ...(over.encryptionEnabled !== undefined && { encryptionEnabled: over.encryptionEnabled }),
    ...(over.repoStorage !== undefined && { repoStorage: over.repoStorage }),
  };
  const client = await createMeshClient(options);
  clients.push(client);
  return client;
}

afterEach(async () => {
  for (const c of clients) {
    try {
      await c.close();
    } catch {
      // best effort
    }
  }
  clients.length = 0;
  FakeWebSocket.reset();
  FakePeerConnection.reset();
});

// ─── Construction & wiring ─────────────────────────────────────────────────────

describe("createMeshClient — construction", () => {
  test("returns a fully wired client whose pieces are exposed", async () => {
    const client = await make();
    expect(client.repo).toBeDefined();
    expect(client.signaling).toBeDefined();
    expect(client.networkAdapter).toBeDefined();
    expect(client.webrtcAdapter).toBeDefined();
    expect(typeof client.close).toBe("function");
    expect(client.selfRevocation).toBeUndefined();
  });

  test("the Repo's peerId matches the signalling peer id (signature lookups)", async () => {
    const client = await make();
    expect(client.repo.peerId as unknown as string).toBe(LOCAL);
  });

  test("the keyring getter reads through the live source", async () => {
    const keyring = makeKeyring();
    const client = await make({ keyring });
    expect(client.keyring).toBe(keyring);
  });

  test("sends the join frame on the signalling socket once open", async () => {
    await make();
    const join = FakeWebSocket.last().sent.map((s) => JSON.parse(s));
    expect(join).toContainEqual({ type: "join", peerId: LOCAL });
  });
});

describe("createMeshClient — keyring source shapes", () => {
  test("accepts a { source } callback and reads through it", async () => {
    const keyring = makeKeyring();
    const client = await make({ keyring: { source: () => keyring } });
    expect(client.keyring).toBe(keyring);
  });

  test("accepts a { storage } adapter and loads the keyring once", async () => {
    const keyring = makeKeyring();
    let loads = 0;
    const client = await make({
      keyring: {
        storage: {
          load: async () => {
            loads += 1;
            return keyring;
          },
          save: async () => {},
        },
      },
    });
    expect(client.keyring).toBe(keyring);
    expect(loads).toBe(1);
  });

  test("throws a bootstrap-pointing error when storage returns null", async () => {
    await expect(
      make({
        keyring: { storage: { load: async () => null, save: async () => {} } },
      })
    ).rejects.toThrow(/no saved keyring|bootstrap/i);
  });
});

describe("createMeshClient — encryption guard", () => {
  test("throws when encryption is enabled but no document key is present", async () => {
    await expect(make({ keyring: makeKeyring({ documentKeys: new Map() }) })).rejects.toThrow(
      new RegExp(`no document key for "${DEFAULT_MESH_KEY_ID}"`)
    );
  });

  test("constructs in sign-only mode when encryption is disabled (no doc key needed)", async () => {
    const client = await make({
      encryptionEnabled: false,
      keyring: makeKeyring({ documentKeys: new Map() }),
    });
    expect(client.repo).toBeDefined();
  });
});

describe("createMeshClient — rtc option forwarding", () => {
  // The forwarded options land on the WebRTC adapter; asserting the adapter's
  // resolved config kills the conditional-spread mutants that would silently
  // drop each option. (Forcing a spread to fire with `undefined` is an
  // equivalent mutant — `{ x: undefined }` resolves to the same default — so
  // these assertions target the drop/empty/inversion mutants, not those.)
  test("forwards every rtc option onto the adapter when present", async () => {
    const iceServers = [{ urls: "stun:stun.example.com" }];
    const client = await make({
      rtc: {
        RTCPeerConnection: FakePC,
        iceServers,
        iceTransportPolicy: "relay",
        iceRelayEnforcement: false,
        dataChannelLabel: "custom-label",
        knownPeersRefreshIntervalMs: 1234,
        syncYieldEnabled: false,
        syncFragmentChunkSizeOverride: 65536,
      },
    });
    const adapter = client.webrtcAdapter;
    expect(adapter.iceServers).toEqual(iceServers);
    expect(adapter.iceTransportPolicy).toBe("relay");
    expect(adapter.dataChannelLabel).toBe("custom-label");
    expect(client.getPeerStateSnapshot().sweep.intervalMs).toBe(1234);
    // The remaining forwarded options are private; reach in deliberately so
    // the spread that carries them is pinned (same approach the peer-relay
    // test uses for Repo internals).
    const internals = adapter as unknown as {
      iceRelayEnforcement: boolean;
      syncYieldEnabled: boolean;
      syncFragmentChunkSize: number;
    };
    expect(internals.iceRelayEnforcement).toBe(false);
    expect(internals.syncYieldEnabled).toBe(false);
    expect(internals.syncFragmentChunkSize).toBe(65536);
  });

  test("applies adapter defaults when rtc options are omitted", async () => {
    // Only RTCPeerConnection is injected; every other rtc option is absent, so
    // the adapter must fall back to its documented defaults. This pins the
    // "absent" side of each conditional spread against a mutant that forces it.
    const client = await make({ rtc: { RTCPeerConnection: FakePC } });
    const adapter = client.webrtcAdapter;
    expect(adapter.iceTransportPolicy).toBeUndefined();
    expect(adapter.dataChannelLabel).toBe("polly-mesh");
    expect(client.getPeerStateSnapshot().sweep.intervalMs).toBe(2000);
  });

  test("an iceCredentialResolver wins over a static iceServers list", async () => {
    let resolved = 0;
    const resolverServers = [{ urls: "turn:turn.example.com", username: "u", credential: "c" }];
    const client = await make({
      rtc: {
        RTCPeerConnection: FakePC,
        knownPeersRefreshIntervalMs: 0,
        iceServers: [{ urls: "stun:ignored" }],
        iceCredentialResolver: async () => {
          resolved += 1;
          return resolverServers;
        },
      },
    });
    expect(resolved).toBe(1);
    // The resolver's servers reach the adapter, not the static list.
    expect(client.webrtcAdapter.iceServers).toEqual(resolverServers);
  });

  test("forwards signalling onError and onCustomFrame hooks", async () => {
    const custom: unknown[] = [];
    const errors: string[] = [];
    const client = await make({
      signaling: {
        url: "ws://localhost:9/sig",
        peerId: LOCAL,
        WebSocket: FakeWS,
        onError: (reason) => errors.push(reason),
        onCustomFrame: (frame) => custom.push(frame),
      },
    });
    const ws = FakeWebSocket.last();
    ws.fireMessage({ type: "app-custom", hello: "world" });
    ws.fireMessage({ type: "error", reason: "boom" });
    expect(custom).toHaveLength(1);
    expect(errors).toEqual(["boom"]);
    expect(client.signaling).toBeDefined();
  });
});

describe("createMeshClient — knownPeers seeding", () => {
  test("seeds the adapter with keyring peers, excluding the local id", async () => {
    // L875-876: the factory filters the local peer out of the keyring's
    // knownPeers before seeding the adapter. A keyring carrying both the
    // local id and a remote pins both the filter predicate and the array.
    const remotePub = generateSigningKeyPair().publicKey;
    const keyring = makeKeyring({
      knownPeers: new Map([
        [LOCAL, generateSigningKeyPair().publicKey],
        ["remote-x", remotePub],
      ]),
    });
    const client = await make({ keyring });
    expect(client.webrtcAdapter.knownPeerIds).toEqual(["remote-x"]);
  });
});

// ─── Returned surface ──────────────────────────────────────────────────────────

describe("createMeshClient — returned methods", () => {
  test("getPeerStateSnapshot reports the local peer with no peers connected", async () => {
    const snap = (await make()).getPeerStateSnapshot();
    expect(snap.localPeerId).toBe(LOCAL);
    expect(snap.peers).toEqual([]);
    expect(snap.repoHandleIds).toEqual(snap.repoHandleIds); // present, array
    expect(Array.isArray(snap.repoHandleIds)).toBe(true);
  });

  test("refreshKnownPeers and reevaluateAllSync resolve without a connection", async () => {
    const client = await make();
    expect(() => client.refreshKnownPeers()).not.toThrow();
    await expect(client.reevaluateAllSync()).resolves.toBeUndefined();
  });

  test("refreshTransportStats resolves with no peers", async () => {
    await expect((await make()).refreshTransportStats()).resolves.toBeUndefined();
  });

  test("close is idempotent and tears the socket down", async () => {
    const client = await make();
    await client.close();
    await client.close();
    expect(FakeWebSocket.last().closeCalls).toBeGreaterThanOrEqual(1);
  });
});

// ─── Revocation & connected-peer lifecycle ──────────────────────────────────────

interface ControlSend {
  tag: MeshControlType;
  targets: PeerId[];
}

/** Spy on the network adapter's control-message path so a test can assert
 * what revokePeer / the peer-candidate gossip actually put on the wire. */
function spyControlSends(client: MeshClient): ControlSend[] {
  const sends: ControlSend[] = [];
  const na = client.networkAdapter;
  const real = na.sendControlMessage.bind(na);
  na.sendControlMessage = ((tag, body, targets) => {
    sends.push({ tag: tag as MeshControlType, targets: [...targets] });
    return real(tag, body, targets);
  }) as typeof na.sendControlMessage;
  return sends;
}

describe("createMeshClient — revocation lifecycle", () => {
  test("a peer-candidate event registers the peer and gossips a revocation summary", async () => {
    const client = await make();
    const sends = spyControlSends(client);
    const peerId = "remote-peer" as PeerId;
    // The network adapter is the connected-peer source; emit the lifecycle
    // event the WebRTC data channel would raise on open.
    (client.networkAdapter as unknown as { emit: (e: string, p: unknown) => void }).emit(
      "peer-candidate",
      { peerId }
    );
    // peer-candidate kicks off the summary gossip to the new peer.
    expect(sends).toContainEqual({ tag: MESH_CONTROL_TYPE.RevocationSummary, targets: [peerId] });
  });

  test("revokePeer broadcasts a revocation to every connected peer", async () => {
    const client = await make();
    const peerId = "remote-peer" as PeerId;
    (client.networkAdapter as unknown as { emit: (e: string, p: unknown) => void }).emit(
      "peer-candidate",
      { peerId }
    );
    const sends = spyControlSends(client);
    await client.revokePeer(peerId, "compromised");
    expect(client.keyring.revokedPeers.has(peerId)).toBe(true);
    expect(sends).toContainEqual({ tag: MESH_CONTROL_TYPE.Revocation, targets: [peerId] });
  });

  test("a peer-disconnected event drops the peer so revokePeer skips the broadcast", async () => {
    const client = await make();
    const peerId = "remote-peer" as PeerId;
    const na = client.networkAdapter as unknown as { emit: (e: string, p: unknown) => void };
    na.emit("peer-candidate", { peerId });
    na.emit("peer-disconnected", { peerId });
    const sends = spyControlSends(client);
    await client.revokePeer(peerId);
    expect(client.keyring.revokedPeers.has(peerId)).toBe(true);
    // No connected peers remain, so no Revocation control message goes out.
    expect(sends.filter((s) => s.tag === MESH_CONTROL_TYPE.Revocation)).toEqual([]);
  });

  test("revokePeer with no connected peers mutates the keyring and skips the broadcast", async () => {
    const client = await make();
    const sends = spyControlSends(client);
    await client.revokePeer("absent-peer");
    expect(client.keyring.revokedPeers.has("absent-peer")).toBe(true);
    expect(sends).toEqual([]);
  });
});

// ─── Signalling discovery callbacks ─────────────────────────────────────────────

describe("createMeshClient — signalling discovery wiring", () => {
  test("peers-present and peer-joined for an unknown peer are safe no-ops", async () => {
    const client = await make();
    const ws = FakeWebSocket.last();
    ws.fireMessage({ type: "peers-present", peerIds: ["unknown-peer"] });
    ws.fireMessage({ type: "peer-joined", peerId: "unknown-peer" });
    ws.fireMessage({ type: "peer-left", peerId: "unknown-peer" });
    // No dial is initiated for a peer absent from knownPeers.
    await new Promise((r) => setTimeout(r, 0));
    expect(client.getPeerStateSnapshot().peers).toEqual([]);
  });

  test("a peer-joined frame routes through to the adapter and initiates a dial", async () => {
    // The signalling onPeerJoined callback must forward to the WebRTC adapter.
    // A known remote with a lower id than the local peer means the local side
    // is the initiator, so the dial fires an offer back out over the socket —
    // an observable effect that pins the callback body (L937-938).
    const remote = "aaa-remote"; // < "local-peer", so LOCAL initiates
    const keyring = makeKeyring({
      knownPeers: new Map([[remote, generateSigningKeyPair().publicKey]]),
    });
    const client = await make({ keyring });
    const ws = FakeWebSocket.last();
    ws.fireMessage({ type: "peer-joined", peerId: remote });
    await new Promise((r) => setTimeout(r, 0));
    const signalFrames = ws.sent
      .map((s) => JSON.parse(s))
      .filter((f) => f.type === "signal" && f.targetPeerId === remote);
    expect(signalFrames.length).toBeGreaterThanOrEqual(1);
    expect(client.getPeerStateSnapshot().presentPeerIds).toContain(remote);
  });
});

// ─── Repo storage ───────────────────────────────────────────────────────────────

describe("createMeshClient — repo storage", () => {
  test("wires the supplied storage adapter into the Repo", async () => {
    const fakeStorage = {
      load: async () => undefined,
      save: async () => {},
      remove: async () => {},
      loadRange: async () => [],
      removeRange: async () => {},
    };
    const client = await make({ repoStorage: fakeStorage as never });
    expect(
      Boolean((client.repo as unknown as { storageSubsystem?: unknown }).storageSubsystem)
    ).toBe(true);
  });

  test("leaves the Repo in-memory when no storage is supplied", async () => {
    const client = await make();
    expect(
      Boolean((client.repo as unknown as { storageSubsystem?: unknown }).storageSubsystem)
    ).toBe(false);
  });
});

// ─── Inbound revocation control messages ────────────────────────────────────────

/** A base network adapter that records what the adapter above it sends and
 * lets a test replay those bytes into another adapter's receive path. */
class CapturingBaseAdapter extends NetworkAdapter {
  sent: Message[] = [];
  isReady(): boolean {
    return true;
  }
  whenReady(): Promise<void> {
    return Promise.resolve();
  }
  connect(peerId: PeerId): void {
    this.peerId = peerId;
  }
  disconnect(): void {}
  send(message: Message): void {
    this.sent.push(message);
  }
}

/** Build a remote "issuer" whose signed control messages the client trusts:
 * it shares the client's document key and its signing public key is added to
 * the client's keyring. Returns a function that signs a control message and
 * returns the on-the-wire bytes the client's base adapter would receive. */
function makeIssuer(
  issuerId: string,
  issuerIdentity: SigningKeyPair,
  docKey: Uint8Array
): (tag: MeshControlType, body: Uint8Array, targetId: string) => Message {
  const base = new CapturingBaseAdapter();
  const adapter = new MeshNetworkAdapter({
    base,
    keyringSource: () => ({
      identity: issuerIdentity,
      knownPeers: new Map(),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    }),
    encryptionEnabled: true,
  });
  adapter.connect(issuerId as PeerId);
  return (tag, body, targetId) => {
    base.sent.length = 0;
    adapter.sendControlMessage(tag, body, [targetId as PeerId]);
    const wire = base.sent.at(-1);
    if (!wire) throw new Error("issuer produced no wire message");
    return wire;
  };
}

describe("createMeshClient — inbound revocation handling", () => {
  const ISSUER = "issuer-peer";
  let unsubscribe: (() => void) | undefined;

  afterEach(() => {
    unsubscribe?.();
    unsubscribe = undefined;
  });

  async function setup(): Promise<{
    client: MeshClient;
    issuerIdentity: SigningKeyPair;
    sign: ReturnType<typeof makeIssuer>;
    deliver: (msg: Message) => void;
    diagnostics: MeshDiagnostic[];
  }> {
    const issuerIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();
    const keyring = makeKeyring({
      knownPeers: new Map([[ISSUER, issuerIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    });
    const client = await make({ keyring });
    const sign = makeIssuer(ISSUER, issuerIdentity, docKey);
    // mesh diagnostics are a global emitter; capture them so the control
    // handlers' observable output (revoke:applied / self-targeted / duplicate /
    // rejected) can be asserted. Unsubscribed in afterEach.
    const diagnostics: MeshDiagnostic[] = [];
    unsubscribe = subscribeToMeshDiagnostics((d) => diagnostics.push(d));
    // The client's base adapter is the WebRTC adapter; replaying a message on
    // its "message" event drives the MeshNetworkAdapter receive path, which
    // unwraps control frames to the factory's onControlMessage handler.
    const deliver = (msg: Message): void => {
      (client.webrtcAdapter as unknown as { emit: (e: string, m: Message) => void }).emit(
        "message",
        msg
      );
    };
    return { client, issuerIdentity, sign, deliver, diagnostics };
  }

  test("applies a revocation that targets a third peer", async () => {
    const { client, issuerIdentity, sign, deliver, diagnostics } = await setup();
    const record = createRevocation({ issuerPeerId: ISSUER, revokedPeerId: "victim-peer" });
    deliver(sign(MESH_CONTROL_TYPE.Revocation, encodeRevocation(record, issuerIdentity), LOCAL));
    expect(client.keyring.revokedPeers.has("victim-peer")).toBe(true);
    expect(
      diagnostics.some((d) => d.kind === "revoke:applied" && d.revokedPeerId === "victim-peer")
    ).toBe(true);
  });

  test("records a self-targeted revocation without silencing the local keyring", async () => {
    const { client, issuerIdentity, sign, deliver, diagnostics } = await setup();
    const record = createRevocation({
      issuerPeerId: ISSUER,
      revokedPeerId: LOCAL,
      reason: "rotated",
    });
    deliver(sign(MESH_CONTROL_TYPE.Revocation, encodeRevocation(record, issuerIdentity), LOCAL));
    expect(client.selfRevocation?.revokedPeerId).toBe(LOCAL);
    expect(client.selfRevocation?.reason).toBe("rotated");
    // Self-revocation does not add the local peer to its own revoked set.
    expect(client.keyring.revokedPeers.has(LOCAL)).toBe(false);
    expect(diagnostics.some((d) => d.kind === "revoke:self-targeted")).toBe(true);
  });

  test("re-delivery of an applied revocation is classified as a duplicate", async () => {
    const { issuerIdentity, sign, deliver, diagnostics } = await setup();
    const record = createRevocation({ issuerPeerId: ISSUER, revokedPeerId: "victim-peer" });
    const wire = sign(
      MESH_CONTROL_TYPE.Revocation,
      encodeRevocation(record, issuerIdentity),
      LOCAL
    );
    deliver(wire);
    diagnostics.length = 0;
    deliver(wire);
    expect(diagnostics.some((d) => d.kind === "revoke:duplicate")).toBe(true);
  });

  test("a malformed revocation body is rejected, not applied", async () => {
    const { client, sign, deliver, diagnostics } = await setup();
    // A valid outer envelope (signed by the trusted issuer) carrying bytes that
    // are not a decodable revocation record: decodeRevocation throws and the
    // handler emits revoke:rejected rather than mutating the keyring.
    deliver(sign(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1, 2, 3, 4]), LOCAL));
    expect(diagnostics.some((d) => d.kind === "revoke:rejected")).toBe(true);
    expect(client.keyring.revokedPeers.size).toBe(0);
  });

  test("a revocation summary that omits a held revocation triggers a push-back", async () => {
    const { client, issuerIdentity, sign, deliver } = await setup();
    // The client holds a revocation for victim-peer.
    const record = createRevocation({ issuerPeerId: ISSUER, revokedPeerId: "victim-peer" });
    deliver(sign(MESH_CONTROL_TYPE.Revocation, encodeRevocation(record, issuerIdentity), LOCAL));
    const sends = spyControlSends(client);
    // The issuer's summary lists nothing, so the client must push its held
    // revocation back to converge the two sides.
    deliver(sign(MESH_CONTROL_TYPE.RevocationSummary, encodeRevocationSummary([]), LOCAL));
    expect(sends.some((s) => s.tag === MESH_CONTROL_TYPE.Revocation)).toBe(true);
  });
});
