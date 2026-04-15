/**
 * Phase 2 revocation tests.
 *
 * Covers the three layers of the revocation story:
 *
 *   1. RevocationRecord construction and the binary envelope that
 *      signs, serialises, decodes, and verifies it.
 *
 *   2. applyRevocation and revokePeerLocally mutating a MeshKeyring.
 *
 *   3. End-to-end enforcement through MeshNetworkAdapter: a peer whose
 *      id is in the receiver's revokedPeers set has its messages
 *      silently dropped at the receiving adapter, even though its
 *      public key is still in the receiver's knownPeers map.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId, Repo } from "@automerge/automerge-repo";
import { generateDocumentKey } from "@/shared/lib/encryption";
import {
  DEFAULT_MESH_KEY_ID,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "@/shared/lib/mesh-network-adapter";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import {
  applyRevocation,
  createRevocation,
  decodeRevocation,
  encodeRevocation,
  RevocationError,
  revokePeerLocally,
} from "@/shared/lib/revocation";
import { generateSigningKeyPair } from "@/shared/lib/signing";

type Doc = { title: string };

beforeEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

afterEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

function makeKeyring(args: {
  identity: ReturnType<typeof generateSigningKeyPair>;
  knownPeers?: Map<string, Uint8Array>;
  documentKeys?: Map<string, Uint8Array>;
}): MeshKeyring {
  return {
    identity: args.identity,
    knownPeers: args.knownPeers ?? new Map(),
    documentKeys: args.documentKeys ?? new Map(),
    revokedPeers: new Set(),
  };
}

class LoopbackAdapter extends NetworkAdapter {
  partner?: LoopbackAdapter;
  #ready = false;

  isReady(): boolean {
    return this.#ready;
  }
  whenReady(): Promise<void> {
    if (this.#ready) return Promise.resolve();
    return new Promise((resolve) => {
      const tick = () => (this.#ready ? resolve() : setTimeout(tick, 5));
      tick();
    });
  }
  connect(peerId: PeerId): void {
    this.peerId = peerId;
    this.#ready = true;
    if (this.partner?.peerId) {
      this.emit("peer-candidate", { peerId: this.partner.peerId, peerMetadata: {} });
      this.partner.emit("peer-candidate", { peerId, peerMetadata: {} });
    }
  }
  disconnect(): void {
    this.#ready = false;
    this.emit("close");
  }
  send(message: Message): void {
    if (!this.partner) return;
    queueMicrotask(() => this.partner?.emit("message", message));
  }
}

function makeLoopbackPair(): [LoopbackAdapter, LoopbackAdapter] {
  const a = new LoopbackAdapter();
  const b = new LoopbackAdapter();
  a.partner = b;
  b.partner = a;
  return [a, b];
}

async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs = 2000
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return;
    await new Promise((r) => setTimeout(r, 10));
  }
  throw new Error(`Timed out after ${timeoutMs}ms`);
}

// ─── Layer 1: RevocationRecord and envelope ─────────────────────────────────

describe("createRevocation", () => {
  test("populates every field from the options", () => {
    const issuer = generateSigningKeyPair();
    const before = Date.now();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
      reason: "compromised at 2026-04-01",
    });
    const after = Date.now();
    expect(record.version).toBe(1);
    expect(record.issuerPeerId).toBe("peer-alice");
    expect(record.revokedPeerId).toBe("peer-mallory");
    expect(record.reason).toBe("compromised at 2026-04-01");
    expect(record.issuedAt).toBeGreaterThanOrEqual(before);
    expect(record.issuedAt).toBeLessThanOrEqual(after);
  });

  test("reason is optional", () => {
    const issuer = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    expect(record.reason).toBeUndefined();
  });
});

describe("encodeRevocation and decodeRevocation", () => {
  test("round-trips a record through binary with signature verification", () => {
    const issuer = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const original = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
      reason: "lost device",
    });

    const encoded = encodeRevocation(original, issuer);

    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([["peer-alice", issuer.publicKey]]),
    });

    const decoded = decodeRevocation(encoded, receiverKeyring);
    expect(decoded.issuerPeerId).toBe(original.issuerPeerId);
    expect(decoded.revokedPeerId).toBe(original.revokedPeerId);
    expect(decoded.reason).toBe(original.reason);
    expect(decoded.issuedAt).toBe(original.issuedAt);
  });

  test("round-trips a record with no reason", () => {
    const issuer = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const original = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-bob",
    });
    const encoded = encodeRevocation(original, issuer);
    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([["peer-alice", issuer.publicKey]]),
    });
    const decoded = decodeRevocation(encoded, receiverKeyring);
    expect(decoded.reason).toBeUndefined();
  });

  test("decodeRevocation throws when the issuer is unknown to the receiver", () => {
    const issuer = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-unknown",
      revokedPeerId: "peer-mallory",
    });
    const encoded = encodeRevocation(record, issuer);

    const receiverKeyring = makeKeyring({ identity: receiver });

    let caught: unknown;
    try {
      decodeRevocation(encoded, receiverKeyring);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(RevocationError);
    expect((caught as RevocationError).code).toBe("unknown-issuer");
  });

  test("accepts any known peer's revocation when revocationAuthority is undefined", () => {
    const issuer = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    const encoded = encodeRevocation(record, issuer);

    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([["peer-alice", issuer.publicKey]]),
    });
    // revocationAuthority is undefined on the default keyring — first-cut
    // behaviour: any known signer is trusted to revoke.
    const decoded = decodeRevocation(encoded, receiverKeyring);
    expect(decoded.revokedPeerId).toBe("peer-mallory");
  });

  test("accepts the issuer's revocation when revocationAuthority contains them", () => {
    const admin = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const record = createRevocation({
      issuer: admin,
      issuerPeerId: "peer-admin",
      revokedPeerId: "peer-mallory",
    });
    const encoded = encodeRevocation(record, admin);

    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([["peer-admin", admin.publicKey]]),
    });
    receiverKeyring.revocationAuthority = new Set(["peer-admin"]);

    const decoded = decodeRevocation(encoded, receiverKeyring);
    expect(decoded.revokedPeerId).toBe("peer-mallory");
  });

  test("rejects an issuer outside the revocationAuthority set", () => {
    const admin = generateSigningKeyPair();
    const random = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const record = createRevocation({
      issuer: random,
      issuerPeerId: "peer-random",
      revokedPeerId: "peer-mallory",
    });
    const encoded = encodeRevocation(record, random);

    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([
        ["peer-admin", admin.publicKey],
        ["peer-random", random.publicKey],
      ]),
    });
    // Only the admin is authorised to issue revocations.
    receiverKeyring.revocationAuthority = new Set(["peer-admin"]);

    let caught: unknown;
    try {
      decodeRevocation(encoded, receiverKeyring);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(RevocationError);
    expect((caught as RevocationError).code).toBe("unauthorised-issuer");
  });

  test("decodeRevocation throws on a tampered payload", () => {
    const issuer = generateSigningKeyPair();
    const receiver = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    const encoded = encodeRevocation(record, issuer);
    // Flip a byte somewhere in the middle of the payload.
    const tampered = encoded.slice();
    const idx = Math.floor(tampered.length / 2);
    tampered[idx] = (tampered[idx] ?? 0) ^ 0xff;

    const receiverKeyring = makeKeyring({
      identity: receiver,
      knownPeers: new Map([["peer-alice", issuer.publicKey]]),
    });

    let caught: unknown;
    try {
      decodeRevocation(tampered, receiverKeyring);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(RevocationError);
    // Tampering anywhere in the signed payload produces either a signature
    // failure or a structural parse error; both are acceptable outcomes.
    const code = (caught as RevocationError).code;
    expect([
      "signature-invalid",
      "truncated",
      "wrong-magic",
      "unknown-version",
      "not-signed-by-issuer",
    ]).toContain(code);
  });
});

// ─── Layer 2: applyRevocation and revokePeerLocally ─────────────────────────

describe("applyRevocation", () => {
  test("adds the target peer id to the keyring's revokedPeers set", () => {
    const issuer = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    const keyring = makeKeyring({ identity: generateSigningKeyPair() });
    applyRevocation(record, keyring);
    expect(keyring.revokedPeers.has("peer-mallory")).toBe(true);
    expect(keyring.revokedPeers.size).toBe(1);
  });

  test("is idempotent on repeated application", () => {
    const issuer = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    const keyring = makeKeyring({ identity: generateSigningKeyPair() });
    applyRevocation(record, keyring);
    applyRevocation(record, keyring);
    expect(keyring.revokedPeers.size).toBe(1);
  });

  test("does not clear knownPeers for the revoked peer", () => {
    const issuer = generateSigningKeyPair();
    const mallory = generateSigningKeyPair();
    const record = createRevocation({
      issuer,
      issuerPeerId: "peer-alice",
      revokedPeerId: "peer-mallory",
    });
    const keyring = makeKeyring({
      identity: generateSigningKeyPair(),
      knownPeers: new Map([["peer-mallory", mallory.publicKey]]),
    });
    applyRevocation(record, keyring);
    // Public key stays — the revocation set is separate from knownPeers so
    // the application can audit who was once authorised.
    expect(keyring.knownPeers.get("peer-mallory")).toEqual(mallory.publicKey);
    expect(keyring.revokedPeers.has("peer-mallory")).toBe(true);
  });
});

describe("revokePeerLocally", () => {
  test("adds the peer id without going through a RevocationRecord", () => {
    const keyring = makeKeyring({ identity: generateSigningKeyPair() });
    revokePeerLocally("peer-mallory", keyring);
    expect(keyring.revokedPeers.has("peer-mallory")).toBe(true);
  });
});

// ─── Layer 3: end-to-end enforcement through MeshNetworkAdapter ─────────────

describe("MeshNetworkAdapter — revocation enforcement", () => {
  test("a document written by a revoked peer never reaches the other side", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    // B's keyring knows about A's public key, but B has also revoked A.
    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(["peer-a"]),
    };

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as PeerId });

    // Wait for base-adapter peer discovery.
    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Doc>({ title: "from-revoked-a" });
    await handleA.whenReady();

    // Give the network time to attempt propagation. Because B's adapter
    // drops every incoming message from peer-a before it reaches the Repo,
    // the document should never land on B.
    await new Promise((r) => setTimeout(r, 250));
    expect(repoB.handles[handleA.documentId]).toBeUndefined();

    await repoA.shutdown();
    await repoB.shutdown();
  });

  test("a peer that was NOT revoked still syncs normally", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(["peer-someone-else"]),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(["peer-someone-else"]),
    };

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Doc>({ title: "from-honest-a" });
    await handleA.whenReady();

    const handleB = await repoB.find<Doc>(handleA.documentId);
    await waitFor(() => handleB.doc().title === "from-honest-a");
    expect(handleB.doc().title).toBe("from-honest-a");

    await repoA.shutdown();
    await repoB.shutdown();
  });

  test("applying a revocation at runtime stops further messages from the target", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    // First, sync a document while everything is trusted.
    const handleA = repoA.create<Doc>({ title: "before-revocation" });
    await handleA.whenReady();
    const handleB = await repoB.find<Doc>(handleA.documentId);
    await waitFor(() => handleB.doc().title === "before-revocation");

    // Now revoke A from B's side.
    revokePeerLocally("peer-a", bKeyring);

    // A writes a new value. B should not pick it up because B now drops
    // incoming messages from peer-a.
    handleA.change((doc) => {
      doc.title = "after-revocation";
    });

    await new Promise((r) => setTimeout(r, 250));
    // B's view of the document should still be the pre-revocation value.
    expect(handleB.doc().title).toBe("before-revocation");

    await repoA.shutdown();
    await repoB.shutdown();
  });
});
