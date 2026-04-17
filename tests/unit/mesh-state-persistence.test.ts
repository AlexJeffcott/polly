/**
 * Regression coverage for Polly issue #52 — $meshState on a lone device
 * lost its data on every page reload because the key → DocumentId map was
 * an in-memory WeakMap that vanished with the Repo. The document bytes
 * survived in the Automerge-Repo storage adapter; the lookup did not.
 *
 * These tests drive the single-device path:
 *   - write via $meshState against Repo A (holding a storage adapter),
 *   - flush the Repo so the writes reach the adapter,
 *   - drop Repo A and construct a fresh Repo B on the same adapter,
 *   - read via $meshState and assert the write is visible.
 *
 * The shared InMemoryStorage implements the full
 * `StorageAdapterInterface` so both Repos see the same byte store. With
 * the pre-#52 in-memory key map, Repo B produced a fresh DocumentId for
 * the same logical key and the expectation failed on an empty initial
 * value. With the fix in place the DocumentId is derived
 * deterministically from the key and Repo B hydrates from storage.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import type { Chunk, StorageKey } from "@automerge/automerge-repo";
import { Repo, type StorageAdapterInterface } from "@automerge/automerge-repo";
import {
  $meshCounter,
  $meshState,
  configureMeshState,
  resetMeshState,
} from "@/shared/lib/mesh-state";
import { migrationRegistry } from "@/shared/lib/migrate-primitive";
import { primitiveRegistry } from "@/shared/lib/primitive-registry";
import type { VersionedDoc } from "@/shared/lib/schema-version";

type Tasks = VersionedDoc & { items: string[] };

/**
 * Minimal in-memory Automerge-Repo storage adapter. Keys are joined with
 * a separator that cannot appear inside a path segment, so the store is a
 * flat Map. `loadRange` and `removeRange` scan the keys; production
 * adapters use prefix indexes, but the test suite never has more than a
 * handful of chunks per doc so a scan is fine.
 */
class InMemoryStorage implements StorageAdapterInterface {
  private readonly chunks = new Map<string, Uint8Array>();

  private join(key: StorageKey): string {
    return key.join("\u0000");
  }

  async load(key: StorageKey): Promise<Uint8Array | undefined> {
    return this.chunks.get(this.join(key));
  }

  async save(key: StorageKey, data: Uint8Array): Promise<void> {
    this.chunks.set(this.join(key), data);
  }

  async remove(key: StorageKey): Promise<void> {
    this.chunks.delete(this.join(key));
  }

  async loadRange(prefix: StorageKey): Promise<Chunk[]> {
    const needle = this.join(prefix);
    const results: Chunk[] = [];
    for (const [joined, data] of this.chunks) {
      if (joined === needle || joined.startsWith(`${needle}\u0000`)) {
        results.push({ key: joined.split("\u0000"), data });
      }
    }
    return results;
  }

  async removeRange(prefix: StorageKey): Promise<void> {
    const needle = this.join(prefix);
    for (const joined of [...this.chunks.keys()]) {
      if (joined === needle || joined.startsWith(`${needle}\u0000`)) {
        this.chunks.delete(joined);
      }
    }
  }
}

const activeRepos: Repo[] = [];

function makeRepo(storage: StorageAdapterInterface): Repo {
  const repo = new Repo({ network: [], storage });
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

describe("$meshState — lone-device persistence across Repo restart", () => {
  test("state written on one Repo survives a reload on a new Repo backed by the same storage", async () => {
    const storage = new InMemoryStorage();

    const repoA = makeRepo(storage);
    configureMeshState(repoA);
    const writer = $meshState<Tasks>("tasks", { items: [] });
    await writer.loaded;
    writer.value = { items: ["first", "second"] };
    // Let the storage subsystem pick up the signal's write before flushing.
    await new Promise((r) => setTimeout(r, 0));
    await repoA.flush();

    resetMeshState();
    primitiveRegistry.clear();
    migrationRegistry.clear();

    const repoB = makeRepo(storage);
    configureMeshState(repoB);
    const reader = $meshState<Tasks>("tasks", { items: [] });
    await reader.loaded;

    expect(reader.value.items).toEqual(["first", "second"]);
  });

  test("$meshCounter on a lone device recovers its value across a reload", async () => {
    const storage = new InMemoryStorage();

    const repoA = makeRepo(storage);
    configureMeshState(repoA);
    const a = $meshCounter("visits", 0);
    await a.loaded;
    a.value = 3;
    await new Promise((r) => setTimeout(r, 0));
    await repoA.flush();

    resetMeshState();
    primitiveRegistry.clear();
    migrationRegistry.clear();

    const repoB = makeRepo(storage);
    configureMeshState(repoB);
    const b = $meshCounter("visits", 0);
    await b.loaded;

    expect(b.value).toBe(3);
  });

  test("a fresh key on a repo without storage seeds without waiting for the unavailable timeout", async () => {
    const repo = new Repo({ network: [] });
    activeRepos.push(repo);
    configureMeshState(repo);

    const started = Date.now();
    const prim = $meshState<Tasks>("fresh", { items: ["seed"] });
    await prim.loaded;
    const elapsed = Date.now() - started;

    // The unavailable-transition timeout is 60s; if the factory were waiting
    // for it, we'd never finish this test. Allow generous slack — anything
    // well under a second is proof the short-circuit path fired.
    expect(elapsed).toBeLessThan(2000);
    expect(prim.value.items).toEqual(["seed"]);
  });
});
