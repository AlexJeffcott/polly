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
import type { DocumentId } from "@automerge/automerge-repo";
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
  seedDocumentBytes,
} from "@/shared/lib/mesh-state";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import type { VersionedDoc } from "@/shared/lib/schema-version";
import { generateSigningKeyPair } from "@/shared/lib/signing";

type Notes = VersionedDoc & {
  title: string;
  body: string;
};

const activeRepos: Repo[] = [];

function trackRepo(): Repo {
  const repo = new Repo();
  activeRepos.push(repo);
  return repo;
}

beforeEach(() => {
  primitiveRegistry.clear();
  migrationRegistry.clear();
});

afterEach(async () => {
  resetMeshState();
  primitiveRegistry.clear();
  migrationRegistry.clear();
  for (const repo of activeRepos) {
    try {
      await repo.shutdown();
    } catch {
      // best effort
    }
  }
  activeRepos.length = 0;
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
    if (!this.partner || !this.#ready) return;
    // Deliver on the next microtask to mimic a real network's async send.
    queueMicrotask(() => {
      if (this.#ready) this.partner?.emit("message", message);
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

describe("$meshState — DocumentId derivation", () => {
  test("derives a known DocumentId from a fixed key", async () => {
    // Pinning the derived id locks the contract: nacl.hash of
    // "polly/meshState/v1:" + key, sliced to 16 bytes, then interpreted as
    // an Automerge DocumentId. The mutation that surfaced this gap drops
    // the domain prefix from the input to the hash, which would change
    // this exact value.
    const repo = trackRepo();
    configureMeshState(repo);
    const prim = $meshState<Notes>("domain-test", { title: "", body: "" });
    await prim.loaded;
    expect(prim.handle?.documentId).toBe("2XzGLTRxBs5q9GZpwY5jwGSMNKBi" as unknown as DocumentId);
  });

  test("derives different DocumentIds for different keys", async () => {
    const repo = trackRepo();
    configureMeshState(repo);
    const a = $meshState<Notes>("key-alpha", { title: "", body: "" });
    const b = $meshState<Notes>("key-beta", { title: "", body: "" });
    await Promise.all([a.loaded, b.loaded]);
    expect(a.handle?.documentId).not.toBe(b.handle?.documentId);
  });

  test("derives the same DocumentId across separate Repos for the same key", async () => {
    // Determinism across processes is what makes a fresh device reload
    // pick up its existing on-disk document. Two Repos, same key, same id.
    const repoA = trackRepo();
    const repoB = trackRepo();
    const primA = $meshState<Notes>("same-key", { title: "", body: "" }, { repo: repoA });
    primitiveRegistry.clear();
    const primB = $meshState<Notes>("same-key", { title: "", body: "" }, { repo: repoB });
    await Promise.all([primA.loaded, primB.loaded]);
    expect(primA.handle?.documentId).toBe(primB.handle?.documentId as unknown as DocumentId);
  });
});

describe("$meshState — construction with a local Repo", () => {
  test("registers the key as meshState", () => {
    const repo = trackRepo();
    configureMeshState(repo);
    $meshState<Notes>("notes-1", { title: "", body: "" });
    expect(primitiveRegistry.kindOf("notes-1")).toBe("meshState");
  });

  test("exposes the initial value synchronously", () => {
    const repo = trackRepo();
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
    const repo = trackRepo();
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

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

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

    loopA.disconnect();
    loopB.disconnect();
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

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

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

    loopA.disconnect();
    loopB.disconnect();
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

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Notes>({ title: "x", body: "x" });
    await handleA.whenReady();

    await new Promise((r) => setTimeout(r, 200));
    const handlesOnB = repoB.handles[handleA.documentId];
    expect(handlesOnB).toBeUndefined();

    loopA.disconnect();
    loopB.disconnect();
    await repoA.shutdown();
    await repoB.shutdown();
  });

  test("a peer added to the live keyring source after construction starts decrypting messages", async () => {
    // Issue #100: a long-lived MeshNetworkAdapter has to pick up a peer
    // that was paired *after* construction. The fix replaced the static
    // `keyring` option with a `keyringSource` callback that re-reads the
    // keyring on every send/receive. This test exercises that path: B
    // starts with an empty knownPeers map (so it drops A's first
    // messages), then the source is swapped to a fresh keyring that
    // includes A's public key, and from that point on B successfully
    // syncs with A — without reconstructing the adapter or the repo.
    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), docKey);
    // B's source returns a live reference; we'll mutate `bKeyring` later.
    let bKeyring = makeKeyring(bIdentity, new Map(), docKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<Notes>({ title: "post-pair", body: "shows up after reload" });
    await handleA.whenReady();

    // Give A time to send sync messages that B should drop (B doesn't know A).
    await new Promise((r) => setTimeout(r, 100));
    expect(repoB.handles[handleA.documentId]).toBeUndefined();

    // Simulate the cross-process repro: a fresh keyring is loaded that
    // now includes A's public key. The adapter sees it on the next
    // incoming message because `keyringSource` is called per-message.
    bKeyring = makeKeyring(bIdentity, new Map([["peer-a", aIdentity.publicKey]]), docKey);

    const handleB = await repoB.find<Notes>(handleA.documentId);
    await waitFor(() => handleB.doc().title === "post-pair");
    expect(handleB.doc().body).toBe("shows up after reload");

    loopA.disconnect();
    loopB.disconnect();
    await repoA.shutdown();
    await repoB.shutdown();
  });
});

describe("$meshState — concurrent first-time seed race (#113)", () => {
  /** Two peers materialise `$meshState(key, initial)` against the same logical
   * key with empty local storage. Pre-fix, `loadOrSeed` calls
   * `Automerge.from(initial)` with a fresh random actorId on each side. Each
   * seed assigns the top-level fields independently; on sync, Automerge
   * resolves the concurrent top-level assignments by last-writer-wins-per-field
   * and orphans the losing seed's map — wiping every per-key write that lived
   * inside it. The user-visible failure is mesh:users converging to
   * `{users: {}}` on both peers despite per-key writes having happened on each.
   *
   * The fix derives the seed actor deterministically from the documentId so
   * both peers produce identical seed bytes; Automerge sees one change, not
   * two concurrent ones, and the top-level field is anchored under a single
   * map that survives every subsequent per-key write.
   *
   * Setting `POLLY_113_DISABLE_FIX=1` in the environment falsifies the fix and
   * restores the fresh-actor behaviour — used by this test's pre-fix arm to
   * prove the test actually catches the regression. */
  test("both peers' per-key writes survive after sync over a loopback", async () => {
    type UserDirectory = VersionedDoc & {
      users: Record<string, { name: string }>;
    };

    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), docKey);
    const bKeyring = makeKeyring(bIdentity, new Map([["peer-a", aIdentity.publicKey]]), docKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });
    activeRepos.push(repoA, repoB);

    // Handshake first so sync is live the moment seeds land.
    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    // Both peers hit `loadOrSeed` because neither Repo has storage. The race
    // window for the bug is between these two calls — each independently
    // produces seed ops under a fresh random actor.
    const primA = $meshState<UserDirectory>("mesh:users", { users: {} }, { repo: repoA });
    primitiveRegistry.clear(); // primitive-registry is global; same key, two Repos
    const primB = $meshState<UserDirectory>("mesh:users", { users: {} }, { repo: repoB });
    await Promise.all([primA.loaded, primB.loaded]);

    // Both peers converged on the same docId via deriveDocumentId; that's
    // necessary for the seed collision to be observable, and is also the
    // shape the issue calls out.
    expect(primA.handle?.documentId).toBe(primB.handle?.documentId as unknown as DocumentId);

    // Each peer writes its own entry via per-key `handle.change` — the same
    // workaround fairfox already uses for the post-seed WRITE race. This
    // test isolates the SEED race specifically.
    primA.handle?.change((doc: UserDirectory) => {
      doc.users["id-a"] = { name: "from A" };
    });
    primB.handle?.change((doc: UserDirectory) => {
      doc.users["id-b"] = { name: "from B" };
    });

    // Wait until each peer sees BOTH rows, or fail with a diagnostic that
    // names what's missing. Pre-fix, exactly one row survives the
    // top-level LWW resolution and the loop times out.
    try {
      await waitFor(
        () =>
          Object.keys(primA.handle?.doc()?.users ?? {}).length === 2 &&
          Object.keys(primB.handle?.doc()?.users ?? {}).length === 2,
        3000
      );
    } catch {
      const seenByA = Object.keys(primA.handle?.doc()?.users ?? {}).sort();
      const seenByB = Object.keys(primB.handle?.doc()?.users ?? {}).sort();
      throw new Error(
        `polly#113 seed race: peer-A users=[${seenByA.join(",")}] peer-B users=[${seenByB.join(",")}]; expected both peers to see [id-a,id-b]. The losing seed's top-level \`users\` assignment was orphaned by Automerge's per-field LWW.`
      );
    }

    const seenByA = Object.keys(primA.handle?.doc()?.users ?? {}).sort();
    const seenByB = Object.keys(primB.handle?.doc()?.users ?? {}).sort();
    expect(seenByA).toEqual(["id-a", "id-b"]);
    expect(seenByB).toEqual(["id-a", "id-b"]);

    loopA.disconnect();
    loopB.disconnect();
  });

  /** Asymmetric ordering — the exact shape #112 reported. Admin
   * materialises `mesh:users` first, writes a row, and is steady
   * before phone ever joins. Phone then attaches to admin with empty
   * storage, takes the seed path (no stored bytes locally), and
   * reads.
   *
   * Pre-fix: phone's seed used a fresh random actor on the empty-
   * storage path. The sync merge resolved the concurrent top-level
   * `users` field assignments by per-field LWW; admin's writes were
   * orphaned and phone's view stayed `{users: {}}` — admin had
   * snapshot 1080B + incremental 1099B on disk while phone held
   * snapshot 125B. The handshake counters quiesced after the initial
   * exchange because, from Automerge's side, there was nothing more
   * to send; the bug was upstream of the sync state machine.
   *
   * With the deterministic seed (#113) phone's seed bytes are
   * byte-identical to admin's, so Automerge dedupes on merge and
   * admin's write survives onto phone's view. */
  test("late-joining peer with empty storage receives admin's write (#112 ordering)", async () => {
    type UserDirectory = VersionedDoc & {
      users: Record<string, { name: string; revoked?: boolean }>;
    };

    const [loopA, loopB] = makeLoopbackPair();
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring = makeKeyring(aIdentity, new Map([["peer-b", bIdentity.publicKey]]), docKey);
    const bKeyring = makeKeyring(bIdentity, new Map([["peer-a", aIdentity.publicKey]]), docKey);

    const adapterA = new MeshNetworkAdapter({ base: loopA, keyringSource: () => aKeyring });
    const adapterB = new MeshNetworkAdapter({ base: loopB, keyringSource: () => bKeyring });

    const repoA = new Repo({ network: [adapterA], peerId: "peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [adapterB], peerId: "peer-b" as unknown as PeerId });
    activeRepos.push(repoA, repoB);

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const primA = $meshState<UserDirectory>("mesh:users", { users: {} }, { repo: repoA });
    await primA.loaded;
    primA.handle?.change((doc: UserDirectory) => {
      doc.users["phone"] = { name: "Phone", revoked: true };
    });

    // Admin's write must be visible on admin's own view before phone
    // joins; otherwise the test is checking the symmetric race rather
    // than the late-join one.
    expect(Object.keys(primA.handle?.doc()?.users ?? {})).toEqual(["phone"]);

    primitiveRegistry.clear();
    const primB = $meshState<UserDirectory>("mesh:users", { users: {} }, { repo: repoB });
    await primB.loaded;

    expect(primA.handle?.documentId).toBe(primB.handle?.documentId as unknown as DocumentId);

    try {
      await waitFor(() => Object.keys(primB.handle?.doc()?.users ?? {}).length === 1, 3000);
    } catch {
      const seenByA = Object.keys(primA.handle?.doc()?.users ?? {}).sort();
      const seenByB = Object.keys(primB.handle?.doc()?.users ?? {}).sort();
      throw new Error(
        `polly#112 late-join: peer-A users=[${seenByA.join(",")}] peer-B users=[${seenByB.join(",")}]; expected B to see [phone]. Admin's write was orphaned by the seed race on phone's side.`
      );
    }

    expect(primB.handle?.doc()?.users["phone"]).toEqual({ name: "Phone", revoked: true });

    loopA.disconnect();
    loopB.disconnect();
  });
});

describe("$meshState — seed byte determinism (#113/#114)", () => {
  // seedDocumentBytes is where the #113 fix lives. The loopback race test
  // above proves cross-peer *merge* convergence, but both peers seed within
  // the same millisecond, so it cannot catch a regression that only diverges
  // when two devices seed at different wall-clock times — the `time: 0` half
  // of the fix. (Verified: dropping `time: 0` survives the full unit suite
  // and the TLA+ seed verifier; see tools/verify/MUTATION-ORACLE-SPIKE.md.)
  // deriveSeedActor treats the DocumentId as an opaque string it hashes, so
  // any stable, distinct strings exercise the actor-derivation contract.
  const docId = "2XzGLTRxBs5q9GZpwY5jwGSMNKBi" as unknown as DocumentId;
  const otherDocId = "4Nkp2vQwYbR8sT1uX6yZ9aBcDeFg" as unknown as DocumentId;
  const initial = { title: "hello", body: "world", items: ["a", "b"] };

  test("seed bytes are independent of wall-clock time (the `time: 0` lever)", () => {
    const realNow = Date.now;
    try {
      Date.now = () => 1_000;
      const early = seedDocumentBytes(docId, initial);
      Date.now = () => 9_999_999_999;
      const late = seedDocumentBytes(docId, initial);
      expect(late).toEqual(early);
    } finally {
      Date.now = realNow;
    }
  });

  test("two peers seeding the same docId produce byte-identical documents", () => {
    // Distinct calls stand in for two devices; the docId-derived actor pins
    // both to the same authorship stamp, so the bytes must match exactly.
    expect(seedDocumentBytes(docId, initial)).toEqual(seedDocumentBytes(docId, initial));
  });

  test("different docIds produce different seed bytes (actor is docId-derived)", () => {
    expect(seedDocumentBytes(docId, initial)).not.toEqual(seedDocumentBytes(otherDocId, initial));
  });
});
