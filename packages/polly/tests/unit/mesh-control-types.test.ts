/**
 * Contract test for the RFC-043 control-message type-tag dispatch in
 * MeshNetworkAdapter. Every plaintext payload now begins with a
 * one-byte tag that discriminates Automerge sync from the future
 * revocation flows. This file proves the dispatch is wired correctly:
 *
 *   - Sync (0x00) round-trips an Automerge message unchanged.
 *   - Revocation (0x01) and RevocationSummary (0x02) are recognised
 *     but their payload-apply behaviour is not yet wired; they emit
 *     a `ctrl:*-received` diagnostic and the message is dropped at
 *     this layer.
 *   - Unknown tags (0x03+) emit drop:unknown-control-type and drop.
 *   - An empty payload (no tag byte) emits drop:empty-control-payload.
 *
 * Behaviour: the apply-and-persist paths for revocation and summary
 * land in the next RFC-043 PR. This test will need extending once
 * those handlers exist.
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
  recordMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";
import {
  DEFAULT_MESH_KEY_ID,
  MESH_CONTROL_TYPE,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "../../src/shared/lib/mesh-network-adapter";
import {
  encodeSignedEnvelope,
  generateSigningKeyPair,
  signEnvelope,
} from "../../src/shared/lib/signing";
import { peerId } from "./helpers/branded";

class TestBaseAdapter extends NetworkAdapter {
  isReady(): boolean {
    return true;
  }
  whenReady(): Promise<void> {
    return Promise.resolve();
  }
  connect(peerId: PeerId): void {
    this.peerId = peerId;
  }
  disconnect(): void {
    // no-op
  }
  send(_message: Message): void {
    // no-op
  }
  emitIncoming(message: Message): void {
    this.emit("message", message);
  }
}

function buildKeyring(knownSenders: Map<string, Uint8Array>): MeshKeyring {
  const identity = generateSigningKeyPair();
  const docKey = generateDocumentKey();
  return {
    identity,
    knownPeers: knownSenders,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(),
  };
}

function buildSerialisedSyncMessage(senderId: string): Uint8Array {
  const header = JSON.stringify({ type: "sync", senderId, targetId: "us" });
  const headerBytes = new TextEncoder().encode(header);
  const out = new Uint8Array(4 + headerBytes.length);
  new DataView(out.buffer).setUint32(0, headerBytes.length, false);
  out.set(headerBytes, 4);
  return out;
}

function wrapTaggedPayload(
  tag: number,
  body: Uint8Array,
  senderId: string,
  senderSecret: Uint8Array,
  docKey: Uint8Array
): Uint8Array {
  const tagged = new Uint8Array(1 + body.byteLength);
  tagged[0] = tag;
  tagged.set(body, 1);
  const encrypted = sealEncryptedEnvelope(tagged, DEFAULT_MESH_KEY_ID, docKey);
  const encryptedBytes = encodeEncryptedEnvelope(encrypted);
  const signed = signEnvelope(encryptedBytes, senderId, senderSecret);
  return encodeSignedEnvelope(signed);
}

describe("MeshNetworkAdapter control-type dispatch", () => {
  afterEach(() => {
    clearMeshDiagnosticListeners();
  });

  test("Sync tag forwards the inner Automerge message", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-sync";
    const keyring = buildKeyring(new Map([[senderId, sender.publicKey]]));
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const messages: Message[] = [];
    adapter.on("message", (msg: Message) => {
      messages.push(msg);
    });
    const { events } = recordMeshDiagnostics();

    const inner = buildSerialisedSyncMessage(senderId);
    const bytes = wrapTaggedPayload(
      MESH_CONTROL_TYPE.Sync,
      inner,
      senderId,
      sender.secretKey,
      docKey
    );
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(messages).toHaveLength(1);
    expect(events).toHaveLength(0);
  });

  test("Revocation tag emits ctrl:revocation-received and drops", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-rev";
    const keyring = buildKeyring(new Map([[senderId, sender.publicKey]]));
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const messages: Message[] = [];
    adapter.on("message", (msg: Message) => {
      messages.push(msg);
    });
    const { events } = recordMeshDiagnostics();

    const bytes = wrapTaggedPayload(
      MESH_CONTROL_TYPE.Revocation,
      new Uint8Array([1, 2, 3, 4]),
      senderId,
      sender.secretKey,
      docKey
    );
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(messages).toHaveLength(0);
    expect(events).toHaveLength(1);
    const event = events[0];
    expect(event?.kind).toBe("ctrl:revocation-received");
    if (event?.kind !== "ctrl:revocation-received") throw new Error("unreachable: asserted above");
    expect(event.senderId).toBe(senderId);
  });

  test("RevocationSummary tag emits ctrl:revocation-summary-received and drops", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-sum";
    const keyring = buildKeyring(new Map([[senderId, sender.publicKey]]));
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const messages: Message[] = [];
    adapter.on("message", (msg: Message) => {
      messages.push(msg);
    });
    const { events } = recordMeshDiagnostics();

    const bytes = wrapTaggedPayload(
      MESH_CONTROL_TYPE.RevocationSummary,
      new Uint8Array([9, 9, 9]),
      senderId,
      sender.secretKey,
      docKey
    );
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(messages).toHaveLength(0);
    expect(events).toHaveLength(1);
    expect(events[0]?.kind).toBe("ctrl:revocation-summary-received");
  });

  test("Unknown tag emits drop:unknown-control-type with the tag value", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-unk";
    const keyring = buildKeyring(new Map([[senderId, sender.publicKey]]));
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const messages: Message[] = [];
    adapter.on("message", (msg: Message) => {
      messages.push(msg);
    });
    const { events } = recordMeshDiagnostics();

    const bytes = wrapTaggedPayload(0x42, new Uint8Array([1]), senderId, sender.secretKey, docKey);
    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(messages).toHaveLength(0);
    expect(events).toHaveLength(1);
    const event = events[0];
    expect(event?.kind).toBe("drop:unknown-control-type");
    if (event?.kind !== "drop:unknown-control-type") throw new Error("unreachable: asserted above");
    expect(event.tag).toBe(0x42);
    expect(event.senderId).toBe(senderId);
  });

  test("Empty payload (no tag byte) emits drop:empty-control-payload", () => {
    const base = new TestBaseAdapter();
    const sender = generateSigningKeyPair();
    const senderId = "peer-empty";
    const keyring = buildKeyring(new Map([[senderId, sender.publicKey]]));
    const docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) throw new Error("test setup missing doc key");
    const adapter = new MeshNetworkAdapter({ base, keyringSource: () => keyring });

    const messages: Message[] = [];
    adapter.on("message", (msg: Message) => {
      messages.push(msg);
    });
    const { events } = recordMeshDiagnostics();

    // Hand-build an envelope whose inner payload is empty.
    const encrypted = sealEncryptedEnvelope(new Uint8Array(0), DEFAULT_MESH_KEY_ID, docKey);
    const encryptedBytes = encodeEncryptedEnvelope(encrypted);
    const signed = signEnvelope(encryptedBytes, senderId, sender.secretKey);
    const bytes = encodeSignedEnvelope(signed);

    base.emitIncoming({
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("us"),
      data: bytes,
    });

    expect(messages).toHaveLength(0);
    expect(events).toHaveLength(1);
    expect(events[0]?.kind).toBe("drop:empty-control-payload");
  });

  test("Sync round-trip through the adapter end-to-end (wrap then unwrap)", () => {
    // Build two adapters sharing a keyring so a real send() goes through
    // wrap() and the receive goes through tryUnwrap(). Confirms the
    // type-tag stays internal — no consumer code needs to touch it.
    const ident = generateSigningKeyPair();
    const senderId = "peer-roundtrip";
    const docKey = generateDocumentKey();
    const keyring: MeshKeyring = {
      identity: ident,
      knownPeers: new Map([[senderId, ident.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    // Side A and side B share the same identity for the loopback; the
    // adapter does not care that the receiver is also the signer.
    const baseA = new TestBaseAdapter();
    const baseB = new TestBaseAdapter();
    const adapterA = new MeshNetworkAdapter({ base: baseA, keyringSource: () => keyring });
    const _adapterB = new MeshNetworkAdapter({
      base: baseB,
      keyringSource: () => keyring,
    });

    let captured: Message | undefined;
    baseA.send = (msg: Message) => {
      // Hand A's send straight to B's receive.
      baseB.emitIncoming(msg);
    };
    _adapterB.on("message", (msg: Message) => {
      captured = msg;
    });

    const original: Message = {
      type: "sync",
      senderId: peerId(senderId),
      targetId: peerId("peer-roundtrip"),
      data: new Uint8Array([4, 5, 6, 7]),
    };
    adapterA.send(original);

    expect(captured).toBeDefined();
    expect(captured?.type).toBe("sync");
    expect(captured?.senderId).toBe(peerId(senderId));
    expect(Array.from(captured?.data ?? [])).toEqual([4, 5, 6, 7]);
  });
});
