/**
 * Integration tests for the polly#112 diagnostic structural reader.
 *
 * The unit test in {@link ./mesh-client-sync-view-112.test.ts} drives
 * `buildSyncView` with hand-built stubs — useful for the degrade paths
 * but it cannot catch the highest-risk failure mode: that the
 * structural cast in the reader points at the wrong Automerge
 * internals. If `repo.synchronizer.docSynchronizers[id].hasPeer` is
 * actually exposed under a different name (or behind a getter with
 * side effects, or `@hidden` in a way that doesn't survive the cast),
 * the unit test would still pass and every snapshot in production
 * would silently report `docSynchronizerExists: false` for every doc.
 *
 * These tests build a real Automerge `Repo`, drive a real peer
 * through a loopback NetworkAdapter, and assert the diagnostic
 * fields reflect what's actually there.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { type Message, NetworkAdapter, type PeerId, Repo } from "@automerge/automerge-repo";
import { __test__ } from "@/shared/lib/mesh-client";

const { buildSyncView, getCollectionSynchronizer, enrichPeerSlot, EMPTY_SYNC_VIEW } = __test__;

// ─── Loopback NetworkAdapter — lifted from revocation.test.ts ───────────────

class LoopbackAdapter extends NetworkAdapter {
  partner?: LoopbackAdapter;
  #ready = false;

  isReady(): boolean {
    return this.#ready;
  }
  whenReady(): Promise<void> {
    if (this.#ready) return Promise.resolve();
    return new Promise((resolve) => {
      const tick = (): void => {
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
    queueMicrotask(() => {
      if (this.#ready) this.partner?.emit("message", message);
    });
  }
}

async function waitFor(predicate: () => boolean, timeoutMs = 2000): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (predicate()) return;
    await new Promise((r) => setTimeout(r, 10));
  }
  throw new Error(`Timed out after ${timeoutMs}ms waiting for predicate`);
}

const activeRepos: Repo[] = [];
const activeAdapters: LoopbackAdapter[] = [];

function trackRepo(repo: Repo): Repo {
  activeRepos.push(repo);
  return repo;
}

function trackAdapter(a: LoopbackAdapter): LoopbackAdapter {
  activeAdapters.push(a);
  return a;
}

afterEach(async () => {
  for (const a of activeAdapters) {
    try {
      a.disconnect();
    } catch {
      // best effort
    }
  }
  activeAdapters.length = 0;
  for (const r of activeRepos) {
    try {
      await r.shutdown();
    } catch {
      // best effort
    }
  }
  activeRepos.length = 0;
});

// ─── Tests ──────────────────────────────────────────────────────────────────

describe("getCollectionSynchronizer (#112 integration)", () => {
  test("returns the real synchronizer object off a constructed Repo", () => {
    const repo = trackRepo(new Repo());
    const sync = getCollectionSynchronizer(repo);
    // The single most load-bearing assertion: Automerge actually
    // exposes `synchronizer` on the Repo and our structural cast finds
    // it. If this ever fails after an Automerge bump, the entire #112
    // diagnostic silently degrades to EMPTY_SYNC_VIEW for every entry.
    expect(sync).toBeDefined();
    expect(typeof sync?.docSynchronizers).toBe("object");
  });
});

describe("buildSyncView (#112 integration — real Repo)", () => {
  test("a freshly-imported handle gets a docSynchronizer entry", () => {
    const repo = trackRepo(new Repo());
    const handle = repo.create<{ value: number }>({ value: 1 });
    const docId = handle.documentId as unknown as string;

    const sync = getCollectionSynchronizer(repo);
    const view = buildSyncView(sync, docId, "any-peer-not-connected");
    // This is the critical positive integration claim: when a handle
    // is in `repo.handles`, the diagnostic reports
    // `docSynchronizerExists: true`. If Automerge's
    // `CollectionSynchronizer` ever renames `docSynchronizers`, this
    // test fails loudly.
    expect(view.docSynchronizerExists).toBe(true);
    // No peer is connected, so the docSynchronizer doesn't know any
    // peer yet — the symmetric #107 gap shape, but here it's expected
    // because we genuinely haven't added one.
    expect(view.docSynchronizerKnowsPeer).toBe(false);
    expect(view.peerDocumentStatus).toBeUndefined();
  });

  test("an unknown docId reports docSynchronizerExists: false", () => {
    const repo = trackRepo(new Repo());
    repo.create<{ value: number }>({ value: 1 }); // some other doc

    const sync = getCollectionSynchronizer(repo);
    const view = buildSyncView(sync, "not-a-real-doc-id", "any-peer");
    // No docSynchronizer for the queried docId — surface the empty
    // view. This guards against a future refactor accidentally
    // returning `docSynchronizerExists: true` for every lookup.
    expect(view).toEqual(EMPTY_SYNC_VIEW);
  });

  test("a connected peer becomes known to the docSynchronizer with status 'has' after sync", async () => {
    // The positive end-to-end shape: when sync completes for a (doc,
    // peer) pair, `peerDocumentStatus` advances from "unknown" to
    // "has". This proves the field name on Automerge's side is
    // correct AND that our reader returns Automerge's actual values
    // (not just whatever string we happened to inject).
    const [loopA, loopB] = [
      trackAdapter(new LoopbackAdapter()),
      trackAdapter(new LoopbackAdapter()),
    ];
    loopA.partner = loopB;
    loopB.partner = loopA;
    const repoA = trackRepo(new Repo({ network: [loopA], peerId: "peer-a" as unknown as PeerId }));
    const repoB = trackRepo(new Repo({ network: [loopB], peerId: "peer-b" as unknown as PeerId }));

    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0);

    const handleA = repoA.create<{ value: number }>({ value: 42 });
    await handleA.whenReady();
    const docIdA = handleA.documentId as unknown as string;

    const handleB = await repoB.find<{ value: number }>(handleA.documentId);
    await waitFor(() => handleB.doc().value === 42);

    const syncA = getCollectionSynchronizer(repoA);
    const viewA = buildSyncView(syncA, docIdA, "peer-b");
    expect(viewA.docSynchronizerExists).toBe(true);
    expect(viewA.docSynchronizerKnowsPeer).toBe(true);
    // Automerge sets status to "has" once heads have been exchanged
    // far enough that the local side knows the peer holds the doc.
    expect(viewA.peerDocumentStatus).toBe("has");

    // Symmetric on the other side.
    const syncB = getCollectionSynchronizer(repoB);
    const viewB = buildSyncView(syncB, docIdA, "peer-a");
    expect(viewB.docSynchronizerExists).toBe(true);
    expect(viewB.docSynchronizerKnowsPeer).toBe(true);
    expect(viewB.peerDocumentStatus).toBe("has");
  });

  test("a doc not shared with the peer reports the symmetric polly#107 gap", async () => {
    // Construct a single Repo with one handle and no peer. We assert
    // the "docSynchronizer exists, peer not registered" shape — the
    // exact fingerprint the #112 hypothesis predicts mesh:users will
    // show in fairfox's failing e2e.
    const repo = trackRepo(new Repo({ peerId: "peer-solo" as unknown as PeerId }));
    const handle = repo.create<{ value: number }>({ value: 99 });
    const docId = handle.documentId as unknown as string;
    await handle.whenReady();

    const sync = getCollectionSynchronizer(repo);
    const view = buildSyncView(sync, docId, "phantom-peer-never-connected");

    expect(view.docSynchronizerExists).toBe(true);
    expect(view.docSynchronizerKnowsPeer).toBe(false);
    expect(view.peerDocumentStatus).toBeUndefined();
  });
});

describe("enrichPeerSlot (#112 surface wiring)", () => {
  test("threads the per-(docId, peerId) view onto each per-handle entry", () => {
    // The structural reader is correct, but a typo in the snapshot
    // factory would drop the new fields entirely. Drive enrichPeerSlot
    // directly with a fake adapter peer shape AND a real synchronizer,
    // and confirm the output entry carries the three new fields.
    const repo = trackRepo(new Repo());
    const handle = repo.create<{ value: number }>({ value: 7 });
    const docId = handle.documentId as unknown as string;

    const syncForRead = getCollectionSynchronizer(repo);

    const fakePeer = {
      peerId: "peer-fake",
      slot: {
        handles: {
          [docId]: {
            lastSyncMessageOutAt: 123,
            lastSyncMessageInAt: undefined,
            lastSyncMessageOutSize: 256,
            lastSyncMessageOutType: "sync",
          },
        },
      },
    } as unknown as Parameters<typeof enrichPeerSlot>[0];

    const repoHandles = repo.handles as unknown as Record<string, { state: unknown } | undefined>;
    const enriched = enrichPeerSlot(fakePeer, [docId], repoHandles, syncForRead);
    const entry = enriched.slot?.handles[docId];

    expect(entry).toBeDefined();
    // Pre-existing fields still work.
    expect(entry?.announcedToPeer).toBe(true);
    expect(entry?.lastSyncMessageOutAt).toBe(123);
    // Three new #112 fields land on the entry.
    expect(entry?.docSynchronizerExists).toBe(true);
    expect(entry?.docSynchronizerKnowsPeer).toBe(false);
    expect(entry?.peerDocumentStatus).toBeUndefined();
  });

  test("entries for docs the local Repo doesn't hold still get the empty sync view", () => {
    // The wire saw a sync message for an unknown documentId. The
    // existing path stamps `state: "unknown"`; the new #112 path
    // should leave docSynchronizerExists at false and not crash.
    const repo = trackRepo(new Repo());
    const syncForRead = getCollectionSynchronizer(repo);

    const fakePeer = {
      peerId: "peer-fake",
      slot: {
        handles: {
          "unknown-doc-id": {
            lastSyncMessageOutAt: undefined,
            lastSyncMessageInAt: 999,
            lastSyncMessageOutSize: undefined,
            lastSyncMessageOutType: undefined,
          },
        },
      },
    } as unknown as Parameters<typeof enrichPeerSlot>[0];

    const repoHandles = repo.handles as unknown as Record<string, { state: unknown } | undefined>;
    const enriched = enrichPeerSlot(fakePeer, [], repoHandles, syncForRead);
    const entry = enriched.slot?.handles["unknown-doc-id"];

    expect(entry).toBeDefined();
    expect(entry?.state).toBe("unknown");
    expect(entry?.docSynchronizerExists).toBe(false);
    expect(entry?.docSynchronizerKnowsPeer).toBeUndefined();
    expect(entry?.peerDocumentStatus).toBeUndefined();
  });
});
