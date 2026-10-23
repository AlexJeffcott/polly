/**
 * Contract test for the diagnostic stream wired through MeshNetworkAdapter.
 *
 * Each of the seven silent-drop branches in `tryUnwrap` must emit exactly
 * one diagnostic of the documented kind, with the documented context
 * fields. The adapter's drop behaviour is preserved — the network path
 * still returns undefined and the Repo never sees a corrupted message —
 * but every drop is now observable through `subscribeToMeshDiagnostics`.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId } from "@automerge/automerge-repo/slim";
import {
  encodeEncryptedEnvelope,
  generateDocumentKey,
  sealEnvelope as sealEncryptedEnvelope,
} from "../../src/shared/lib/encryption";
import {
  clearMeshDiagnosticListeners,
  type MeshDiagnosticEvent,
  recordMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";
import {
  DEFAULT_MESH_KEY_ID,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "../../src/shared/lib/mesh-network-adapter";
import {
  encodeSignedEnvelope,
  generateSigningKeyPair,
  signEnvelope,
} from "../../src/shared/lib/signing";
import { peerId } from "./helpers/branded";

/**
 * Minimal NetworkAdapter that lets the test drive incoming 'message'
 * events directly. The mesh adapter wraps this and observes whatever the
 * test emits on it.
 */
class TestBaseAdapter extends NetworkAdapter {
  #ready = true;

  isReady(): boolean {
    return this.#ready;
  }
  whenReady(): Promise<void> {
    return Promise.resolve();
  }
  connect(peerId: PeerId): void {
    this.peerId = peerId;
  }
  disconnect(): void {
    this.#ready = false;
  }
  send(_message: Message): void {
    // No-op: this test never reads what the adapter sends.
  }
  emitIncoming(message: Message): void {
    this.emit("message", message);
  }
}

function buildKeyring(overrides: Partial<MeshKeyring> = {}): MeshKeyring {
  const identity = generateSigningKeyPair();
  const docKey = generateDocumentKey();
  return {
    identity,
    knownPeers: new Map(),
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(),
    ...overrides,
  };
}

function makeValidSignedBytes(
  senderId: string,
  senderSecret: Uint8Array,
  docKeyId: string,
  docKey: Uint8Array,
  innerPayload: Uint8Array
): Uint8Array {
  const encrypted = sealEncryptedEnvelope(innerPayload, docKeyId, docKey);
  const encryptedBytes = encodeEncryptedEnvelope(encrypted);
  const signed = signEnvelope(encryptedBytes, senderId, senderSecret);
  return encodeSignedEnvelope(signed);
}

/** A Sync-tagged (RFC-043 tag 0x00) plaintext whose body is a 4-byte
 * big-endian header length, the header bytes, then `data`. The length
 * prefix is taken from `headerLen` when given, so a test can lie about it. */
function syncTaggedPayload(
  headerBytes: Uint8Array,
  data: Uint8Array = new Uint8Array(0),
  headerLen: number = headerBytes.length
): Uint8Array {
  const out = new Uint8Array(1 + 4 + headerBytes.length + data.length);
  out[0] = 0x00; // MESH_CONTROL_TYPE.Sync
  new DataView(out.buffer).setUint32(1, headerLen, false);
  out.set(headerBytes, 5);
  out.set(data, 5 + headerBytes.length);
  return out;
}

function jsonBytes(value: unknown): Uint8Array {
  return new TextEncoder().encode(JSON.stringify(value));
}

/** A receiver that knows one sender, plus the delivered-message capture. */
function malformedSyncHarness(senderId: string): {
  base: TestBaseAdapter;
  delivered: Message[];
  send: (inner: Uint8Array) => void;
} {
  const base = new TestBaseAdapter();
  const sender = generateSigningKeyPair();
  const keyring = buildKeyring({ knownPeers: new Map([[senderId, sender.publicKey]]) });
  const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
  if (!docKey) throw new Error("test setup missing doc key");
  const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });
  const delivered: Message[] = [];
  adapter.on("message", (m) => {
    delivered.push(m);
  });
  const send = (inner: Uint8Array): void => {
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: makeValidSignedBytes(senderId, sender.secretKey, DEFAULT_MESH_KEY_ID, docKey, inner),
    });
  };
  return { base, delivered, send };
}

describe("MeshNetworkAdapter diagnostic emissions", () => {
  afterEach(() => {
    clearMeshDiagnosticListeners();
  });

  test("malformed signed envelope emits drop:malformed-signed-envelope", () => {
    const base = new TestBaseAdapter();
    const keyring = buildKeyring();
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId("any"),
      targetId: peerId("us"),
      data: new Uint8Array([1, 2, 3, 4]),
    });

    expect(events).toHaveLength(1);
    expect(events[0]?.kind).toBe("drop:malformed-signed-envelope");
  });

  test("revoked peer emits drop:revoked-peer with senderId", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "revoked-peer-1";
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, sender.publicKey]]),
      revokedPeers: new Set([senderId]),
    });
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const docKeyId = DEFAULT_MESH_KEY_ID;
    const docKey = keyring.documentKeys.get(docKeyId);
    if (!docKey) throw new Error("test setup missing doc key");

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      docKeyId,
      docKey,
      new Uint8Array([0])
    );

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:revoked-peer");
    if (ev?.kind !== "drop:revoked-peer") throw new Error("unreachable: asserted above");
    expect(ev.senderId).toBe(senderId);
  });

  test("unknown peer emits drop:unknown-peer with senderId", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "stranger";
    const keyring = buildKeyring(); // no known peers
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      DEFAULT_MESH_KEY_ID,
      docKey,
      new Uint8Array([0])
    );

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:unknown-peer");
    if (ev?.kind !== "drop:unknown-peer") throw new Error("unreachable: asserted above");
    expect(ev.senderId).toBe(senderId);
  });

  test("wrong public key emits drop:bad-signature with senderId", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const imposter = generateSigningKeyPair();
    const senderId = "peer-w";
    // Keyring has the imposter's public key under the senderId; the message
    // is signed by the real sender. Signature verification fails.
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, imposter.publicKey]]),
    });
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      DEFAULT_MESH_KEY_ID,
      docKey,
      new Uint8Array([0])
    );

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:bad-signature");
    if (ev?.kind !== "drop:bad-signature") throw new Error("unreachable: asserted above");
    expect(ev.senderId).toBe(senderId);
  });

  test("malformed encrypted envelope emits drop:malformed-encrypted-envelope", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-mee";
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, sender.publicKey]]),
    });
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    // Sign garbage that won't decode as an encrypted envelope.
    const signed = signEnvelope(new Uint8Array([0xff, 0xff, 0xff]), senderId, sender.secretKey);
    const bytes = encodeSignedEnvelope(signed);

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:malformed-encrypted-envelope");
    if (ev?.kind !== "drop:malformed-encrypted-envelope") {
      throw new Error("unreachable: asserted above");
    }
    expect(ev.senderId).toBe(senderId);
  });

  test("missing doc key emits drop:missing-doc-key with documentId", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-mdk";
    // Receiver has no document key registered under the id used by the sender.
    const senderDocKey = generateDocumentKey();
    const senderDocKeyId = "doc-x";
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, sender.publicKey]]),
      documentKeys: new Map(), // empty — no keys at all
    });
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      senderDocKeyId,
      senderDocKey,
      new Uint8Array([0])
    );

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:missing-doc-key");
    if (ev?.kind !== "drop:missing-doc-key") throw new Error("unreachable: asserted above");
    expect(ev.senderId).toBe(senderId);
    expect(ev.documentId).toBe(senderDocKeyId);
  });

  test("wrong doc key emits drop:bad-decryption with documentId", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-bd";
    // Sender encrypts under key A; receiver has key B under the same id.
    const senderDocKey = generateDocumentKey();
    const receiverDocKey = generateDocumentKey();
    const sharedDocKeyId = "doc-y";
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, sender.publicKey]]),
      documentKeys: new Map([[sharedDocKeyId, receiverDocKey]]),
    });
    new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      sharedDocKeyId,
      senderDocKey,
      new Uint8Array([0])
    );

    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toHaveLength(1);
    const ev = events[0];
    expect(ev?.kind).toBe("drop:bad-decryption");
    if (ev?.kind !== "drop:bad-decryption") throw new Error("unreachable: asserted above");
    expect(ev.senderId).toBe(senderId);
    expect(ev.documentId).toBe(sharedDocKeyId);
  });

  test("a successful message emits no diagnostic", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-ok";
    const keyring = buildKeyring({
      knownPeers: new Map([[senderId, sender.publicKey]]),
    });
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({
      base,
      keyringSource: () => keyring,
    });

    // The inner payload must begin with the Sync control-type tag (RFC-043)
    // followed by a valid serialised Message (length-prefixed JSON header +
    // binary). Send a minimal but valid one.
    const headerObj = {
      type: "sync",
      senderId,
      targetId: "us",
    };
    const headerBytes = new TextEncoder().encode(JSON.stringify(headerObj));
    const serialised = new Uint8Array(4 + headerBytes.length);
    new DataView(serialised.buffer).setUint32(0, headerBytes.length, false);
    serialised.set(headerBytes, 4);
    const inner = new Uint8Array(1 + serialised.byteLength);
    inner[0] = 0x00; // MESH_CONTROL_TYPE.Sync
    inner.set(serialised, 1);

    const bytes = makeValidSignedBytes(
      senderId,
      sender.secretKey,
      DEFAULT_MESH_KEY_ID,
      docKey,
      inner
    );

    const seen: MeshDiagnosticEvent[] = [];
    adapter.on("message", () => {
      /* re-emit success path */
    });
    const { events } = recordMeshDiagnostics();
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(events).toEqual(seen);
    expect(events).toHaveLength(0);
  });

  describe("drop:malformed-sync-message", () => {
    const cases: Array<{ name: string; inner: Uint8Array; reason: string }> = [
      {
        name: "a header without string type, senderId and targetId",
        inner: syncTaggedPayload(jsonBytes({ type: 5, senderId: "peer-ms" })),
        reason: "MeshNetworkAdapter: message header lacks a string type, senderId or targetId.",
      },
      {
        name: "a header that is a JSON array",
        inner: syncTaggedPayload(jsonBytes(["sync", "peer-ms", "us"])),
        reason: "MeshNetworkAdapter: message header is not an object.",
      },
      {
        name: "a non-string documentId",
        inner: syncTaggedPayload(
          jsonBytes({ type: "sync", senderId: "peer-ms", targetId: "us", documentId: 7 })
        ),
        reason: "MeshNetworkAdapter: message header documentId is not a string.",
      },
      {
        name: "a header that is not JSON",
        inner: syncTaggedPayload(new TextEncoder().encode("{not json")),
        reason: "JSON",
      },
      {
        name: "a length prefix longer than the body",
        inner: syncTaggedPayload(jsonBytes({ type: "sync" }), new Uint8Array(0), 999),
        reason: "MeshNetworkAdapter: message header truncated.",
      },
      {
        name: "a body shorter than the length prefix itself",
        inner: new Uint8Array([0x00, 0x00, 0x01]),
        reason: "MeshNetworkAdapter: message too short to deserialise.",
      },
    ];

    for (const c of cases) {
      test(`${c.name} is dropped with one drop:malformed-sync-message`, () => {
        const senderId = "peer-ms";
        const { delivered, send } = malformedSyncHarness(senderId);
        const { events } = recordMeshDiagnostics();

        expect(() => send(c.inner)).not.toThrow();

        expect(delivered).toHaveLength(0);
        expect(events).toHaveLength(1);
        const ev = events[0];
        expect(ev?.kind).toBe("drop:malformed-sync-message");
        if (ev?.kind !== "drop:malformed-sync-message") {
          throw new Error("unreachable: asserted above");
        }
        expect(ev.senderId).toBe(senderId);
        expect(ev.reason).toContain(c.reason);
      });
    }

    test("a well-formed Sync message on the same adapter still delivers", () => {
      const senderId = "peer-ms";
      const { delivered, send } = malformedSyncHarness(senderId);
      const { events } = recordMeshDiagnostics();

      send(syncTaggedPayload(jsonBytes({ type: 5, senderId, targetId: "us" })));
      send(
        syncTaggedPayload(
          jsonBytes({ type: "sync", senderId, targetId: "us", documentId: "doc-ok" }),
          new Uint8Array([9, 8, 7])
        )
      );

      expect(events.map((e) => e.kind)).toEqual(["drop:malformed-sync-message"]);
      expect(delivered).toHaveLength(1);
      expect(delivered[0]).toMatchObject({
        type: "sync",
        senderId,
        targetId: "us",
        documentId: "doc-ok",
        data: new Uint8Array([9, 8, 7]),
      });
    });
  });
});
