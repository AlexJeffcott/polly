/**
 * Unit tests for `sweepSealed` — storage-adapter GC of sealed mesh-doc
 * bytes (polly#121).
 *
 * Covers the issue's acceptance criteria: a sealed + handle-free + old
 * document is removed; a sealed-but-open document is kept; a
 * sealed-but-recent document is kept; an unsealed document is never
 * touched; `dryRun` reports candidates (id, sealed-at, byte size)
 * without deleting; and the PeerRepoServer convenience method delegates
 * to the standalone function with its repo and storage bound.
 */

import { afterEach, describe, expect, test } from "bun:test";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
// Imported first: @automerge/automerge self-initialises its WASM runtime
// at module-eval, so every Automerge call below is ready to run.
import * as Automerge from "@automerge/automerge";
import type {
  Chunk,
  DocumentId,
  Repo,
  StorageAdapterInterface,
  StorageKey,
} from "@automerge/automerge-repo";
import { createPeerRepoServer, type PeerRepoServer } from "@/shared/lib/peer-repo-server";
import { sweepSealed } from "@/shared/lib/sweep-sealed";

// ─── In-memory storage adapter ──────────────────────────────────────────────

/** Minimal StorageAdapterInterface backed by a Map, for driving the sweep. */
class MemoryStorage implements StorageAdapterInterface {
  readonly data = new Map<string, Uint8Array>();

  async load(key: StorageKey): Promise<Uint8Array | undefined> {
    return this.data.get(JSON.stringify(key));
  }

  async save(key: StorageKey, value: Uint8Array): Promise<void> {
    this.data.set(JSON.stringify(key), value);
  }

  async remove(key: StorageKey): Promise<void> {
    this.data.delete(JSON.stringify(key));
  }

  async loadRange(prefix: StorageKey): Promise<Chunk[]> {
    const out: Chunk[] = [];
    for (const [serialised, value] of this.data) {
      const key = JSON.parse(serialised) as StorageKey;
      if (hasPrefix(key, prefix)) out.push({ key, data: value });
    }
    return out;
  }

  async removeRange(prefix: StorageKey): Promise<void> {
    for (const serialised of [...this.data.keys()]) {
      const key = JSON.parse(serialised) as StorageKey;
      if (hasPrefix(key, prefix)) this.data.delete(serialised);
    }
  }
}

function hasPrefix(key: StorageKey, prefix: StorageKey): boolean {
  return prefix.every((part, i) => key[i] === part);
}

/** Brand a plain string as a DocumentId for expectation literals. */
function docId(value: string): DocumentId {
  return value as DocumentId;
}

// ─── Helpers ────────────────────────────────────────────────────────────────

type SealSentinel = { __compaction__?: { sealedAt: number } };

/** Recognises the test's sentinel shape — stands in for a consumer's detector. */
function isSealed(doc: unknown): number | undefined {
  const sentinel = (doc as SealSentinel).__compaction__;
  return typeof sentinel?.sealedAt === "number" ? sentinel.sealedAt : undefined;
}

/** Build the storage bytes of a document, optionally carrying the sentinel. */
function docBytes(mutate: (doc: Record<string, unknown>) => void): Uint8Array {
  let doc = Automerge.init<Record<string, unknown>>();
  doc = Automerge.change(doc, (d) => mutate(d as Record<string, unknown>));
  return Automerge.save(doc);
}

/** Write a document to storage under a snapshot chunk key. */
async function seedDoc(
  storage: MemoryStorage,
  documentId: string,
  mutate: (doc: Record<string, unknown>) => void
): Promise<void> {
  await storage.save([documentId, "snapshot", "heads"], docBytes(mutate));
}

/** A sealed document — carries the sentinel with the given seal time. */
function sealed(sealedAt: number) {
  return (doc: Record<string, unknown>) => {
    doc["__compaction__"] = { sealedAt };
    doc["payload"] = "stale";
  };
}

/** An ordinary, never-sealed document. */
const unsealed = (doc: Record<string, unknown>) => {
  doc["payload"] = "live";
};

/** A Repo whose only relevant surface — its open handles — is the given set. */
function repoWithHandles(...openDocIds: string[]): Repo {
  const handles: Record<string, unknown> = {};
  for (const id of openDocIds) handles[id] = {};
  return { handles } as unknown as Repo;
}

// ─── Standalone sweepSealed ─────────────────────────────────────────────────

describe("sweepSealed", () => {
  test("removes a sealed, handle-free, old document", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "doc-old", sealed(1_000));

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 1_000 + 60_000,
    });

    expect(result.swept.map((s) => s.documentId)).toEqual([docId("doc-old")]);
    expect(result.kept).toEqual([]);
    expect(result.dryRun).toBe(false);
    // Bytes are gone from storage.
    expect(await storage.loadRange(["doc-old"])).toEqual([]);
  });

  test("keeps a sealed document that still has an open handle", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "doc-open", sealed(1_000));

    const result = await sweepSealed({
      repo: repoWithHandles("doc-open"),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 1_000 + 60_000, // old enough — but the handle gate wins
    });

    expect(result.swept).toEqual([]);
    expect(result.kept).toEqual([{ documentId: docId("doc-open"), reason: "open-handle" }]);
    expect((await storage.loadRange(["doc-open"])).length).toBe(1);
  });

  test("keeps a sealed document sealed too recently", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "doc-recent", sealed(1_000));

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 1_000 + 500, // only 500ms old, window is 5_000ms
    });

    expect(result.swept).toEqual([]);
    expect(result.kept).toEqual([{ documentId: docId("doc-recent"), reason: "too-recent" }]);
    expect((await storage.loadRange(["doc-recent"])).length).toBe(1);
  });

  test("never touches or reports an unsealed document", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "doc-plain", unsealed);

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 0, // even with no age window, an unsealed doc is left alone
      now: () => 1_000 + 60_000,
    });

    expect(result.swept).toEqual([]);
    expect(result.kept).toEqual([]);
    expect((await storage.loadRange(["doc-plain"])).length).toBe(1);
  });

  test("dryRun reports candidates — id, sealed-at, byte size — without deleting", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "doc-dry", sealed(1_000));

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 1_000 + 60_000,
      dryRun: true,
    });

    expect(result.dryRun).toBe(true);
    expect(result.swept).toHaveLength(1);
    const candidate = result.swept[0];
    expect(candidate?.documentId).toBe(docId("doc-dry"));
    expect(candidate?.sealedAt).toBe(1_000);
    expect(candidate?.byteSize).toBeGreaterThan(0);
    // dryRun must not have touched storage.
    expect((await storage.loadRange(["doc-dry"])).length).toBe(1);
  });

  test("sorts a mixed store into the right buckets and removes only the eligible doc", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "old", sealed(1_000)); // sealed, free, old   → swept
    await seedDoc(storage, "open", sealed(1_000)); // sealed, handle    → kept
    await seedDoc(storage, "recent", sealed(59_000)); // sealed, recent → kept
    await seedDoc(storage, "plain", unsealed); // unsealed              → ignored

    const result = await sweepSealed({
      repo: repoWithHandles("open"),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 60_000,
    });

    expect(result.swept.map((s) => s.documentId)).toEqual([docId("old")]);
    expect(result.kept).toEqual([
      { documentId: docId("open"), reason: "open-handle" },
      { documentId: docId("recent"), reason: "too-recent" },
    ]);
    expect((await storage.loadRange(["old"])).length).toBe(0);
    expect((await storage.loadRange(["open"])).length).toBe(1);
    expect((await storage.loadRange(["recent"])).length).toBe(1);
    expect((await storage.loadRange(["plain"])).length).toBe(1);
  });

  test("considers only the given documentIds, loading each by its own prefix", async () => {
    const storage = new MemoryStorage();
    await seedDoc(storage, "listed", sealed(1_000));
    await seedDoc(storage, "unlisted", sealed(1_000)); // sealed + old, but not listed

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 60_000,
      documentIds: ["listed"],
    });

    // Only the listed document is swept; the unlisted one is never inspected.
    expect(result.swept.map((s) => s.documentId)).toEqual([docId("listed")]);
    expect((await storage.loadRange(["listed"])).length).toBe(0);
    expect((await storage.loadRange(["unlisted"])).length).toBe(1);
  });

  test("skips a document whose bytes fail to load, without throwing", async () => {
    const storage = new MemoryStorage();
    await storage.save(["doc-corrupt", "snapshot", "x"], new Uint8Array([1, 2, 3, 4]));
    await seedDoc(storage, "doc-old", sealed(1_000));

    const result = await sweepSealed({
      repo: repoWithHandles(),
      storage,
      isSealed,
      olderThan: 5_000,
      now: () => 60_000,
    });

    // The corrupt doc is neither swept nor kept; the valid sealed doc still is.
    expect(result.swept.map((s) => s.documentId)).toEqual([docId("doc-old")]);
    expect(result.kept).toEqual([]);
    expect((await storage.loadRange(["doc-corrupt"])).length).toBe(1);
  });
});

// ─── PeerRepoServer.sweepSealed convenience method ──────────────────────────

describe("PeerRepoServer.sweepSealed", () => {
  let server: PeerRepoServer | undefined;
  let storageDir: string | undefined;

  afterEach(async () => {
    await server?.close();
    server = undefined;
    if (storageDir) await rm(storageDir, { recursive: true, force: true });
    storageDir = undefined;
  });

  test("delegates to the standalone sweep with the server's repo and storage", async () => {
    storageDir = await mkdtemp(join(tmpdir(), "polly-sweep-"));
    server = await createPeerRepoServer({ port: 0, storagePath: storageDir });

    // Empty store: the method is wired, runs, and reports nothing to do.
    const result = await server.sweepSealed({
      isSealed,
      olderThan: 1_000,
      dryRun: true,
    });

    expect(result).toEqual({ swept: [], kept: [], dryRun: true });
  });
});
