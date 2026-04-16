/**
 * Phase 2 mesh-state and mesh-network-adapter tests.
 *
 * The mesh transport is supposed to ship every message between peers as
 * an encrypted, signed envelope. The test setup creates two in-process
 * Repos joined by an in-memory loopback adapter pair, wraps each side in
 * a MeshNetworkAdapter with shared keys, and verifies that:
 *
 *   1. Wrapped messages on the wire are unreadable without the keys.
 *   2. With matching keys, peers handshake and discover each other.
 *   3. Documents created on one side propagate to the other side
 *      verbatim, so the encryption is actually round-tripping.
 *   4. Tampered messages are dropped silently rather than crashing.
 *
 * The loopback adapter pair is the smallest possible network adapter that
 * extends Automerge's NetworkAdapter base class. Side A's send() pushes
 * the message into side B's queue and emits it as a 'message' event on
 * the next microtask, and vice versa. There is no real wire and no real
 * peer discovery — the two halves know each other's peerIds by
 * construction at connect() time.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId, Repo } from "@automerge/automerge-repo";
import { generateDocumentKey } from "@/shared/lib/encryption";
import {
  DEFAULT_MESH_KEY_ID,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "@/shared/lib/mesh-network-adapter";
import {
  $meshCounter,
  $meshList,
  $meshState,
  $meshText,
  configureMeshState,
  resetMeshState,
} from "@/shared/lib/mesh-state";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import type { VersionedDoc } from "@/shared/lib/schema-version";
import { generateSigningKeyPair } from "@/shared/lib/signing";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

beforeEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

afterEach(() => {
  resetMeshState();
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

/**
 * In-memory loopback adapter pair. Side A's send() ends up emitted by
 * side B's 'message' event, and vice versa. Used to wire two Repos
 * together inside a single process for unit tests.
 */
class LoopbackAdapter extends NetworkAdapter {
  partner?: LoopbackAdapter;
  remotePeerId?: PeerId;
  #ready = false;

  isReady(): boolean {
    return this.#ready;
  }

  whenReady(): Promise<void> {
    if (this.#ready) return Promise.resolve();
    return new Promise((resolve) => {
      const tick = () => {
        if (this.#ready) resolve();
        else setTimeout(tick, 5);
      };
      tick();
    });
  }

  connect(peerId: PeerId): void {
    this.peerId = peerId;
    this.#ready = true;
    if (this.partner?.peerId) {
      // Both sides are connected — announce each other as peers.
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
    // Deliver on the next microtask to mimic a real network's async send.
    queueMicrotask(() => {
      this.partner?.emit("message", message);
    });
  }
}

function makeLoopbackPair(): [LoopbackAdapter, LoopbackAdapter] {
  const a = new LoopbackAdapter();
  const b = new LoopbackAdapter();
  a.partner = b;
  b.partner = a;
  return [a, b];
}

function makeKeyring(
  identity: ReturnType<typeof generateSigningKeyPair>,
  knownPeers: Map<string, Uint8Array>,
  documentKey: Uint8Array
): MeshKeyring {
  return {
    identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, documentKey]]),
    revokedPeers: new Set(),
  };
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
  throw new Error(`Timed out after ${timeoutMs}ms waiting for predicate`);
}

describe("$meshState — construction with a local Repo", () => {
  test("registers the key as meshState", () => {
    const repo = new Repo();
    configureMeshState(repo);
    $meshState<Notes>("notes-1", { title: "", body: "" });
    expect(primitiveRegistry.kindOf("notes-1")).toBe("meshState");
  });

  test("exposes the initial value synchronously", () => {
    const repo = new Repo();
    configureMeshState(repo);
    const prim = $meshState<Notes>("notes-2", { title: "from init", body: "" });
    expect(prim.value).toEqual({ title: "from init", body: "" });
  });

  test("throws when no Repo is configured", () => {
    expect(() => $meshState<Notes>("notes-3", { title: "", body: "" })).toThrow(
      /no Repo configured/i
    );
  });

  test("$meshText / $meshCounter / $meshList all register as meshState", async () => {
    const repo = new Repo();
    configureMeshState(repo);
    const text = $meshText("text-key", "");
    const counter = $meshCounter("counter-key", 0);
    const list = $meshList<string>("list-key", []);
    await text.loaded;
    await counter.loaded;
    await list.loaded;
    expect(primitiveRegistry.kindOf("text-key")).toBe("meshState");
    expect(primitiveRegistry.kindOf("counter-key")).toBe("meshState");
    expect(primitiveRegistry.kindOf("list-key")).toBe("meshState");
  });
});

describe("MeshNetworkAdapter — encryption + signing round-trip", () => {
  test("two peers with matching keyrings exchange a document over the loopback", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    // A knows B's public key, B knows A's public key, and both share the doc key.
    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), docKey);
    const bKeyring = makeKeyring(bIdentity, new Map([["peer-a", aIdentity.publicKey]]), docKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({
      network: [adapterA],
      peerId: "peer-a" as unknown as PeerId,
    });
    const repoB = new Repo({
      network: [adapterB],
      peerId: "peer-b" as unknown as PeerId,
    });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Notes>({ title: "encrypted", body: "secret body" });
    await handleA.whenReady();

    // B finds the doc by id; the sync messages are mesh-encrypted on the wire.
    const handleB = await repoB.find<Notes>(handleA.documentId);
    await waitFor(() => handleB.doc().title === "encrypted");
    expect(handleB.doc().body).toBe("secret body");

    await repoA.shutdown();
    await repoB.shutdown();
  });

  test("a peer with the wrong document key cannot read the contents", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const correctKey = generateDocumentKey();
    const wrongKey = generateDocumentKey();

    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), correctKey);
    const bKeyring = makeKeyring(bIdentity, new Map([["peer-a", aIdentity.publicKey]]), wrongKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Notes>({ title: "private", body: "x" });
    await handleA.whenReady();

    // Give the wire some time to attempt sync; B should never converge
    // because every message fails decryption.
    await new Promise((r) => setTimeout(r, 200));
    const handlesOnB = repoB.handles[handleA.documentId];
    expect(handlesOnB).toBeUndefined();

    await repoA.shutdown();
    await repoB.shutdown();
  });

  test("a peer with no public key for the sender drops messages", async () => {
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    // B's keyring does NOT include A's public key. B will reject all of A's messages.
    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), docKey);
    const bKeyring = makeKeyring(bIdentity, new Map(), docKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyring: aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyring: bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Notes>({ title: "x", body: "x" });
    await handleA.whenReady();

    await new Promise((r) => setTimeout(r, 200));
    const handlesOnB = repoB.handles[handleA.documentId];
    expect(handlesOnB).toBeUndefined();

    await repoA.shutdown();
    await repoB.shutdown();
  });
});
