/**
 * Tests for MemoryBlobCache — the in-memory blob byte store with LRU
 * eviction and pinning used in bun:test and server contexts.
 *
 * Covers the get/put/has/delete round trip, byte-accurate size accounting,
 * the evict(maxBytes) policy (oldest-first, pinned entries survive even when
 * oldest), and the object-URL lifecycle (cached, revoked on delete, cleared
 * on dispose).
 */

import { describe, expect, test } from "bun:test";
import { MemoryBlobCache } from "@/shared/lib/blob-cache";

const bytes = (n: number, fill = 1): Uint8Array => new Uint8Array(n).fill(fill);

/** Force a deterministic access time so eviction order is not at the mercy
 * of Date.now() resolution across rapid puts. */
function setAccessedAt(cache: MemoryBlobCache, hash: string, at: number): void {
  (cache as unknown as { store: Map<string, { accessedAt: number }> }).store.get(hash)!.accessedAt =
    at;
}

describe("MemoryBlobCache get/put/has/delete", () => {
  test("put then get round-trips the bytes", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(4, 7));
    expect(Array.from((await cache.get("h1")) as Uint8Array)).toEqual([7, 7, 7, 7]);
  });

  test("get returns undefined for a missing hash", async () => {
    const cache = new MemoryBlobCache();
    expect(await cache.get("nope")).toBeUndefined();
  });

  test("has reflects presence", async () => {
    const cache = new MemoryBlobCache();
    expect(await cache.has("h1")).toBe(false);
    await cache.put("h1", bytes(2));
    expect(await cache.has("h1")).toBe(true);
  });

  test("delete removes the entry", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(2));
    await cache.delete("h1");
    expect(await cache.has("h1")).toBe(false);
    expect(await cache.get("h1")).toBeUndefined();
  });
});

describe("MemoryBlobCache size", () => {
  test("sums the byte length of every entry", async () => {
    const cache = new MemoryBlobCache();
    expect(await cache.size()).toBe(0);
    await cache.put("a", bytes(10));
    await cache.put("b", bytes(25));
    expect(await cache.size()).toBe(35);
  });
});

describe("MemoryBlobCache evict", () => {
  test("is a no-op and frees nothing when already under the target", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", bytes(10));
    expect(await cache.evict(100)).toBe(0);
    expect(await cache.has("a")).toBe(true);
  });

  test("drops oldest entries first until the total fits under the target", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("old", bytes(50));
    await cache.put("mid", bytes(50));
    await cache.put("new", bytes(50));
    setAccessedAt(cache, "old", 1);
    setAccessedAt(cache, "mid", 2);
    setAccessedAt(cache, "new", 3);
    // 150 total, target 60: dropping old (→100) then mid (→50) fits.
    const freed = await cache.evict(60);
    expect(freed).toBe(100);
    expect(await cache.has("old")).toBe(false);
    expect(await cache.has("mid")).toBe(false);
    expect(await cache.has("new")).toBe(true);
    expect(await cache.size()).toBe(50);
  });

  test("never evicts a pinned entry, even when it is the oldest", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("old", bytes(50));
    await cache.put("mid", bytes(50));
    await cache.put("new", bytes(50));
    setAccessedAt(cache, "old", 1);
    setAccessedAt(cache, "mid", 2);
    setAccessedAt(cache, "new", 3);
    await cache.pin("old");
    // Target 60: the oldest (old) is pinned, so mid and new are dropped and
    // old survives despite being the least-recently-used.
    const freed = await cache.evict(60);
    expect(freed).toBe(100);
    expect(await cache.has("old")).toBe(true);
    expect(await cache.has("mid")).toBe(false);
    expect(await cache.has("new")).toBe(false);
  });

  test("stops as soon as the total fits, keeping an entry that lands exactly on the target", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("old", bytes(50));
    await cache.put("mid", bytes(50));
    await cache.put("new", bytes(50));
    setAccessedAt(cache, "old", 1);
    setAccessedAt(cache, "mid", 2);
    setAccessedAt(cache, "new", 3);
    // Target 50 == the size of the surviving entry: dropping old then mid
    // lands exactly on the target, so the loop stops and keeps `new`. A
    // strict `<` boundary would overshoot and evict it too.
    await cache.evict(50);
    expect(await cache.has("new")).toBe(true);
    expect(await cache.size()).toBe(50);
  });

  test("unpin re-exposes an entry to eviction", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", bytes(50));
    await cache.put("b", bytes(50));
    setAccessedAt(cache, "a", 1);
    setAccessedAt(cache, "b", 2);
    await cache.pin("a");
    await cache.unpin("a");
    // With the pin lifted, the oldest (a) is evictable again.
    await cache.evict(60);
    expect(await cache.has("a")).toBe(false);
    expect(await cache.has("b")).toBe(true);
  });
});

describe("MemoryBlobCache object URLs", () => {
  test("url returns a stable cached object URL for a present blob", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(3));
    const first = await cache.url("h1");
    expect(typeof first).toBe("string");
    const second = await cache.url("h1");
    // The second call returns the cached URL rather than minting a new one.
    expect(second).toBe(first);
    cache.dispose();
  });

  test("the object URL resolves to the blob's actual bytes", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(3, 9));
    const url = await cache.url("h1");
    if (!url) throw new Error("expected an object URL");
    // Fetching the URL must yield the stored bytes — an empty Blob payload
    // (a dropped `[buffer]` argument) would resolve to zero bytes.
    const got = new Uint8Array(await (await fetch(url)).arrayBuffer());
    expect(Array.from(got)).toEqual([9, 9, 9]);
    cache.dispose();
  });

  test("url returns undefined for a missing blob", async () => {
    const cache = new MemoryBlobCache();
    expect(await cache.url("ghost")).toBeUndefined();
  });

  test("delete drops the entry and its cached URL", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(3));
    const url = await cache.url("h1");
    expect(typeof url).toBe("string");
    await cache.delete("h1");
    // A fresh url() after delete is undefined (entry gone), proving the
    // cached URL was dropped rather than returned stale.
    expect(await cache.url("h1")).toBeUndefined();
  });

  test("dispose clears the store, pins, and URLs", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("h1", bytes(3));
    await cache.pin("h1");
    await cache.url("h1");
    cache.dispose();
    expect(await cache.has("h1")).toBe(false);
    expect(await cache.size()).toBe(0);
  });
});
