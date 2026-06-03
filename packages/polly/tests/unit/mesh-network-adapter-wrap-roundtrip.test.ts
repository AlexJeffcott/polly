/**
 * Round-trip and routing tests for MeshNetworkAdapter's crypto envelope.
 *
 * The diagnostics suite covers tryUnwrap's seven silent-drop branches; this
 * suite covers everything those tests do not reach: the outgoing `wrap`
 * (encrypt+sign and sign-only), the full wrap→unwrap round trip through a
 * second adapter, the RFC-043 control-message path (sendControlMessage +
 * dispatchTaggedPayload + invokeControlHandler), the serialise/deserialise
 * header fields, prependControlTag, and the base-adapter lifecycle
 * forwarding.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId } from "@automerge/automerge-repo/slim";
import { generateDocumentKey } from "../../src/shared/lib/encryption";
import {
  clearMeshDiagnosticListeners,
  type MeshDiagnosticEvent,
  recordMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";
import {
  DEFAULT_MESH_KEY_ID,
  MESH_CONTROL_TYPE,
  type MeshControlType,
  type MeshKeyring,
  MeshNetworkAdapter,
  prependControlTag,
} from "../../src/shared/lib/mesh-network-adapter";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";

class TestBaseAdapter extends NetworkAdapter {
  #ready = true;
  sent: Message[] = [];
  connectedPeerId: PeerId | undefined;
  disconnected = false;

  isReady(): boolean {
    return this.#ready;
  }
  whenReady(): Promise<void> {
    return Promise.resolve();
  }
  connect(peerId: PeerId): void {
    this.peerId = peerId;
    this.connectedPeerId = peerId;
  }
  disconnect(): void {
    this.#ready = false;
    this.disconnected = true;
  }
  send(message: Message): void {
    this.sent.push(message);
  }
  emitIncoming(message: Message): void {
    this.emit("message", message);
  }
}

const SENDER_ID = "sender-peer";

/** Build a sender/receiver pair that share a document key, with the
 * receiver trusting the sender's signing public key. Returns the two
 * adapters plus their base adapters so a test can pump wrapped bytes from
 * one to the other. */
function buildPair(
  opts: {
    encryptionEnabled?: boolean;
    onControlMessage?: (tag: number, body: Uint8Array, senderId: string) => void;
    receiverDocKeys?: Map<string, Uint8Array>;
    senderDocKeys?: Map<string, Uint8Array>;
  } = {}
): {
  sender: MeshNetworkAdapter;
  senderBase: TestBaseAdapter;
  receiver: MeshNetworkAdapter;
  receiverBase: TestBaseAdapter;
  received: Message[];
} {
  const senderIdentity = generateSigningKeyPair();
  const docKey = generateDocumentKey();
  const senderKeyring: MeshKeyring = {
    identity: senderIdentity,
    knownPeers: new Map(),
    documentKeys: opts.senderDocKeys ?? new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(),
  };
  const receiverKeyring: MeshKeyring = {
    identity: generateSigningKeyPair(),
    knownPeers: new Map([[SENDER_ID, senderIdentity.publicKey]]),
    documentKeys: opts.receiverDocKeys ?? new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(),
  };

  const senderBase = new TestBaseAdapter();
  const receiverBase = new TestBaseAdapter();
  const sender = new MeshNetworkAdapter({
    base: senderBase,
    keyringSource: () => senderKeyring,
    encryptionEnabled: opts.encryptionEnabled,
  });
  sender.connect(SENDER_ID as PeerId);
  const receiver = new MeshNetworkAdapter({
    base: receiverBase,
    keyringSource: () => receiverKeyring,
    encryptionEnabled: opts.encryptionEnabled,
    onControlMessage: opts.onControlMessage,
  });
  const received: Message[] = [];
  receiver.on("message", (m: Message) => received.push(m));
  return { sender, senderBase, receiver, receiverBase, received };
}

function makeMessage(over: Partial<Record<string, unknown>> = {}): Message {
  return {
    type: "sync",
    senderId: SENDER_ID,
    targetId: "receiver-peer",
    documentId: "doc-1",
    data: new Uint8Array([1, 2, 3, 4]),
    ...over,
  } as unknown as Message;
}

afterEach(() => {
  clearMeshDiagnosticListeners();
});

describe("MeshNetworkAdapter wrap → unwrap round trip", () => {
  test("a sync message survives the encrypt-then-sign round trip intact", () => {
    const { sender, senderBase, receiverBase, received } = buildPair();
    sender.send(makeMessage({ data: new Uint8Array([9, 8, 7, 6]) }));
    expect(senderBase.sent).toHaveLength(1);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(received).toHaveLength(1);
    const out = received[0] as Message;
    expect(out.type).toBe("sync");
    expect(out.senderId).toBe(SENDER_ID as unknown as Message["senderId"]);
    expect((out as unknown as { documentId?: string }).documentId).toBe("doc-1");
    expect(Array.from(out.data as Uint8Array)).toEqual([9, 8, 7, 6]);
  });

  test("the wrapped outer envelope preserves documentId for the base adapter", () => {
    const { sender, senderBase } = buildPair();
    sender.send(makeMessage({ documentId: "doc-outer" }));
    const outer = senderBase.sent[0] as unknown as { documentId?: string; data?: unknown };
    expect(outer.documentId).toBe("doc-outer");
    expect(outer.data).toBeInstanceOf(Uint8Array);
  });

  test("a message with no documentId produces an outer envelope without one", () => {
    const { sender, senderBase } = buildPair();
    sender.send(makeMessage({ documentId: undefined }));
    const outer = senderBase.sent[0] as unknown as Record<string, unknown>;
    expect("documentId" in outer).toBe(false);
  });

  test("round trips in sign-only mode (no encryption)", () => {
    const { sender, senderBase, receiverBase, received } = buildPair({
      encryptionEnabled: false,
    });
    sender.send(makeMessage({ data: new Uint8Array([5, 5, 5]) }));
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(received).toHaveLength(1);
    expect(Array.from((received[0] as Message).data as Uint8Array)).toEqual([5, 5, 5]);
  });

  test("throws when encryption is enabled but the document key is missing", () => {
    const { sender } = buildPair({ senderDocKeys: new Map() });
    expect(() => sender.send(makeMessage())).toThrow("missing document encryption key");
  });
});

describe("MeshNetworkAdapter serialise/deserialise header fields", () => {
  test("preserves count and sessionId across the round trip", () => {
    const { sender, senderBase, receiverBase, received } = buildPair();
    sender.send(makeMessage({ count: 7, sessionId: "sess-9", data: new Uint8Array(0) }));
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    const out = received[0] as unknown as { count?: number; sessionId?: string };
    expect(out.count).toBe(7);
    expect(out.sessionId).toBe("sess-9");
  });

  test("omits count and sessionId when the source message lacks them", () => {
    const { sender, senderBase, receiverBase, received } = buildPair();
    sender.send(makeMessage({ count: undefined, sessionId: undefined }));
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    const out = received[0] as unknown as Record<string, unknown>;
    expect("count" in out).toBe(false);
    expect("sessionId" in out).toBe(false);
  });

  test("serialises a message with no data field as an empty payload", () => {
    // The data guard falls back to an empty Uint8Array when the message has
    // no binary `data`; without it, serialise would set() from undefined and
    // throw on the send path.
    const { sender, senderBase, receiverBase, received } = buildPair();
    expect(() => sender.send(makeMessage({ data: undefined }))).not.toThrow();
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(Array.from((received[0] as Message).data as Uint8Array)).toEqual([]);
  });
});

describe("MeshNetworkAdapter control-message path (RFC-043)", () => {
  test("delivers a revocation control message to onControlMessage, not the message stream", () => {
    const calls: Array<{ tag: number; body: number[]; senderId: string }> = [];
    const { sender, senderBase, receiverBase, received } = buildPair({
      onControlMessage: (tag, body, senderId) =>
        calls.push({ tag, body: Array.from(body), senderId }),
    });
    const { events } = recordMeshDiagnostics();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([42, 43]), [
      SENDER_ID as PeerId,
    ]);
    expect(senderBase.sent).toHaveLength(1);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(received).toHaveLength(0);
    expect(calls).toEqual([
      { tag: MESH_CONTROL_TYPE.Revocation, body: [42, 43], senderId: SENDER_ID },
    ]);
    expect(events.map((e: MeshDiagnosticEvent) => e.kind)).toContain("ctrl:revocation-received");
  });

  test("routes a revocation-summary tag to its own diagnostic", () => {
    const calls: number[] = [];
    const { sender, senderBase, receiverBase } = buildPair({
      onControlMessage: (tag) => calls.push(tag),
    });
    const { events } = recordMeshDiagnostics();
    sender.sendControlMessage(MESH_CONTROL_TYPE.RevocationSummary, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(calls).toEqual([MESH_CONTROL_TYPE.RevocationSummary]);
    expect(events.map((e: MeshDiagnosticEvent) => e.kind)).toContain(
      "ctrl:revocation-summary-received"
    );
  });

  test("fans a control message out to every target peer", () => {
    const { sender, senderBase } = buildPair();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
      "peer-1" as PeerId,
      "peer-2" as PeerId,
      "peer-3" as PeerId,
    ]);
    expect(senderBase.sent).toHaveLength(3);
    expect(senderBase.sent.map((m) => String(m.targetId))).toEqual(["peer-1", "peer-2", "peer-3"]);
  });

  test("is a no-op when there are no target peers", () => {
    const { sender, senderBase } = buildPair();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), []);
    expect(senderBase.sent).toHaveLength(0);
  });

  test("swallows a throwing control handler and reports drop:control-handler-threw", () => {
    const { sender, senderBase, receiverBase } = buildPair({
      onControlMessage: () => {
        throw new Error("handler boom");
      },
    });
    const { events } = recordMeshDiagnostics();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    expect(() => receiverBase.emitIncoming(senderBase.sent[0] as Message)).not.toThrow();
    const kinds = events.map((e: MeshDiagnosticEvent) => e.kind);
    expect(kinds).toContain("ctrl:revocation-received");
    expect(kinds).toContain("drop:control-handler-threw");
  });

  test("a control message with no registered handler is dropped without error", () => {
    const { sender, senderBase, receiverBase, received } = buildPair();
    const { events } = recordMeshDiagnostics();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    expect(() => receiverBase.emitIncoming(senderBase.sent[0] as Message)).not.toThrow();
    expect(received).toHaveLength(0);
    expect(events.map((e: MeshDiagnosticEvent) => e.kind)).toContain("ctrl:revocation-received");
  });

  test("an unknown control tag emits drop:unknown-control-type", () => {
    const { sender, senderBase, receiverBase, received } = buildPair();
    const { events } = recordMeshDiagnostics();
    // 0x7f is not a known control type.
    sender.sendControlMessage(0x7f as unknown as MeshControlType, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(received).toHaveLength(0);
    const unknown = events.find(
      (e: MeshDiagnosticEvent) => e.kind === "drop:unknown-control-type"
    ) as (MeshDiagnosticEvent & { tag: number }) | undefined;
    expect(unknown).toBeDefined();
    expect(unknown?.tag).toBe(0x7f);
  });
});

describe("prependControlTag", () => {
  test("prepends the tag byte ahead of the body", () => {
    const out = prependControlTag(MESH_CONTROL_TYPE.Revocation, new Uint8Array([10, 20, 30]));
    expect(out[0]).toBe(MESH_CONTROL_TYPE.Revocation);
    expect(Array.from(out.subarray(1))).toEqual([10, 20, 30]);
    expect(out.byteLength).toBe(4);
  });

  test("handles an empty body", () => {
    const out = prependControlTag(MESH_CONTROL_TYPE.Sync, new Uint8Array(0));
    expect(out.byteLength).toBe(1);
    expect(out[0]).toBe(MESH_CONTROL_TYPE.Sync);
  });
});

describe("MeshNetworkAdapter lifecycle delegation", () => {
  test("forwards close, peer-candidate, and peer-disconnected from the base", () => {
    const base = new TestBaseAdapter();
    const keyring: MeshKeyring = {
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map(),
      revokedPeers: new Set(),
    };
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });
    let closed = false;
    const candidates: unknown[] = [];
    const disconnects: unknown[] = [];
    adapter.on("close", () => {
      closed = true;
    });
    adapter.on("peer-candidate", (p) => candidates.push(p));
    adapter.on("peer-disconnected", (p) => disconnects.push(p));
    base.emit("close");
    base.emit("peer-candidate", {
      peerId: "p1" as PeerId,
      peerMetadata: {},
    });
    base.emit("peer-disconnected", { peerId: "p1" as PeerId });
    expect(closed).toBe(true);
    expect(candidates).toHaveLength(1);
    expect(disconnects).toHaveLength(1);
  });

  test("delegates isReady, whenReady, connect, and disconnect to the base", async () => {
    const base = new TestBaseAdapter();
    const keyring: MeshKeyring = {
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map(),
      revokedPeers: new Set(),
    };
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });
    expect(adapter.isReady()).toBe(true);
    await expect(adapter.whenReady()).resolves.toBeUndefined();
    adapter.connect("me" as PeerId);
    expect(base.connectedPeerId).toBe("me" as PeerId);
    adapter.disconnect();
    expect(base.disconnected).toBe(true);
    expect(adapter.isReady()).toBe(false);
  });

  test("stores peerMetadata when connect is given one", () => {
    const base = new TestBaseAdapter();
    const keyring: MeshKeyring = {
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map(),
      revokedPeers: new Set(),
    };
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });
    const meta = { isEphemeral: false } as unknown as Parameters<typeof adapter.connect>[1];
    adapter.connect("me" as PeerId, meta);
    expect((adapter as unknown as { peerMetadata: unknown }).peerMetadata).toBe(meta);
  });
});

describe("MeshNetworkAdapter edge branches", () => {
  test("the keyring getter returns the current keyring from the source", () => {
    const { receiver } = buildPair();
    expect(receiver.keyring.knownPeers.has(SENDER_ID)).toBe(true);
  });

  test("DEFAULT_MESH_KEY_ID is the documented wire constant", () => {
    expect(DEFAULT_MESH_KEY_ID).toBe("polly-mesh-default");
  });

  test("a message with no data is dropped silently, emitting no diagnostic", () => {
    const { receiverBase, received } = buildPair();
    const { events } = recordMeshDiagnostics();
    receiverBase.emitIncoming({
      type: "sync",
      senderId: SENDER_ID as PeerId,
      targetId: "us" as PeerId,
    } as Message);
    expect(received).toHaveLength(0);
    // The no-data short-circuit returns before any decode is attempted, so
    // unlike a malformed envelope it produces no diagnostic at all.
    expect(events).toHaveLength(0);
  });

  test("delivers a control message with an empty body (the 1-byte tag-only frame)", () => {
    const bodies: number[][] = [];
    const { sender, senderBase, receiverBase } = buildPair({
      onControlMessage: (_tag, body) => bodies.push(Array.from(body)),
    });
    // prependControlTag yields a single tag byte; dispatchTaggedPayload must
    // treat byteLength 1 as a real (empty-body) control frame, not an empty
    // payload to drop.
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array(0), [
      SENDER_ID as PeerId,
    ]);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(bodies).toEqual([[]]);
  });

  test("stamps the outer envelope type as sync for control messages", () => {
    const { sender, senderBase } = buildPair();
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    expect((senderBase.sent[0] as Message).type).toBe("sync");
  });

  test("sendControlMessage round-trips in sign-only mode", () => {
    const tags: number[] = [];
    const { sender, senderBase, receiverBase } = buildPair({
      encryptionEnabled: false,
      onControlMessage: (tag) => tags.push(tag),
    });
    sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
      SENDER_ID as PeerId,
    ]);
    receiverBase.emitIncoming(senderBase.sent[0] as Message);
    expect(tags).toEqual([MESH_CONTROL_TYPE.Revocation]);
  });

  test("sendControlMessage throws when encryption is enabled but the doc key is missing", () => {
    const { sender } = buildPair({ senderDocKeys: new Map() });
    expect(() =>
      sender.sendControlMessage(MESH_CONTROL_TYPE.Revocation, new Uint8Array([1]), [
        SENDER_ID as PeerId,
      ])
    ).toThrow("missing document encryption key");
  });

  test("a Sync payload with a truncated inner frame surfaces the deserialise guard", () => {
    // A Sync-tagged body shorter than the 4-byte length prefix makes
    // deserialiseMessage throw; the throw propagates out of the unwrap.
    const { sender, senderBase, receiverBase } = buildPair({ encryptionEnabled: false });
    // Reach into the sign-only send to craft a Sync frame with a 2-byte body.
    sender.sendControlMessage(MESH_CONTROL_TYPE.Sync, new Uint8Array([1, 2]), [
      SENDER_ID as PeerId,
    ]);
    expect(() => receiverBase.emitIncoming(senderBase.sent[0] as Message)).toThrow(
      "too short to deserialise"
    );
  });

  test("a Sync payload whose header length overruns surfaces the truncated guard", () => {
    const { sender, senderBase, receiverBase } = buildPair({ encryptionEnabled: false });
    // 4-byte length prefix declaring a 100-byte header in a 4-byte body.
    const body = new Uint8Array(4);
    new DataView(body.buffer).setUint32(0, 100, false);
    sender.sendControlMessage(MESH_CONTROL_TYPE.Sync, body, [SENDER_ID as PeerId]);
    expect(() => receiverBase.emitIncoming(senderBase.sent[0] as Message)).toThrow(
      "header truncated"
    );
  });
});
