/**
 * blob-cache — local storage backends for blob bytes.
 *
 * Two implementations:
 * - MemoryBlobCache: in-memory Map, suitable for bun:test and server contexts.
 * - IndexedDBBlobCache: persistent IndexedDB store ("polly-blobs"), for browsers.
 *
 * Both implement the BlobCache interface from blob-store.ts. Neither uses
 * the existing StorageAdapter — ChromeStorageAdapter JSON-serialises values,
 * which silently destroys Uint8Array data. The blob cache uses IndexedDB
 * directly, which stores typed arrays via structured clone.
 *
 * Both support LRU eviction with pinning. Each `get`/`put` updates the
 * entry's access time; `evict(maxBytes)` drops unpinned entries oldest-first
 * until the total size fits under the target.
 */

import type { BlobCache } from "./blob-store";
import { cachedOpen, iterateCursor, runRequest, runTx } from "./idb-helpers";

// MemoryBlobCache

interface MemoryEntry {
  bytes: Uint8Array;
  accessedAt: number;
}

/** In-memory blob cache backed by a Map. No persistence. Suitable for
 *  bun:test (which lacks IndexedDB) and server-side contexts. */
export class MemoryBlobCache implements BlobCache {
  private readonly store = new Map<string, MemoryEntry>();
  private readonly pinned = new Set<string>();
  private readonly urls = new Map<string, string>();

  async get(hash: string): Promise<Uint8Array | undefined> {
    const entry = this.store.get(hash);
    if (!entry) return undefined;
    entry.accessedAt = Date.now();
    return entry.bytes;
  }

  async put(hash: string, bytes: Uint8Array): Promise<void> {
    this.store.set(hash, { bytes, accessedAt: Date.now() });
  }

  async has(hash: string): Promise<boolean> {
    return this.store.has(hash);
  }

  async delete(hash: string): Promise<void> {
    this.store.delete(hash);
    this.pinned.delete(hash);
    const url = this.urls.get(hash);
    if (url) {
      URL.revokeObjectURL(url);
      this.urls.delete(hash);
    }
  }

  async pin(hash: string): Promise<void> {
    this.pinned.add(hash);
  }

  async unpin(hash: string): Promise<void> {
    this.pinned.delete(hash);
  }

  async size(): Promise<number> {
    let total = 0;
    for (const entry of this.store.values()) {
      total += entry.bytes.byteLength;
    }
    return total;
  }

  async evict(maxBytes: number): Promise<number> {
    let currentSize = await this.size();
    if (currentSize <= maxBytes) return 0;
    const freed = currentSize;
    // Sort unpinned entries by accessedAt ascending (oldest first).
    const candidates: Array<{ hash: string; accessedAt: number; size: number }> = [];
    for (const [hash, entry] of this.store) {
      if (!this.pinned.has(hash)) {
        candidates.push({ hash, accessedAt: entry.accessedAt, size: entry.bytes.byteLength });
      }
    }
    candidates.sort((a, b) => a.accessedAt - b.accessedAt);

    for (const c of candidates) {
      if (currentSize <= maxBytes) break;
      await this.delete(c.hash);
      currentSize -= c.size;
    }
    return freed - currentSize;
  }

  /** Create or return a cached object URL for a blob. Returns undefined
   *  if the blob is not in the cache. */
  async url(hash: string): Promise<string | undefined> {
    const cached = this.urls.get(hash);
    if (cached) return cached;
    const entry = this.store.get(hash);
    if (!entry) return undefined;
    const buffer = new ArrayBuffer(entry.bytes.byteLength);
    new Uint8Array(buffer).set(entry.bytes);
    const objectUrl = URL.createObjectURL(new Blob([buffer]));
    this.urls.set(hash, objectUrl);
    return objectUrl;
  }

  dispose(): void {
    for (const objectUrl of this.urls.values()) {
      URL.revokeObjectURL(objectUrl);
    }
    this.urls.clear();
    this.store.clear();
    this.pinned.clear();
  }
}

// IndexedDBBlobCache

interface IDBRecord {
  bytes: Uint8Array;
  size: number;
  accessedAt: number;
  pinned: boolean;
}

/** Persistent blob cache using a dedicated IndexedDB database ("polly-blobs").
 *  Separate from the "polly-state" database used by StorageAdapter. */
export class IndexedDBBlobCache implements BlobCache {
  private static readonly DB_NAME = "polly-blobs";
  private static readonly DB_VERSION = 1;
  private static readonly STORE_NAME = "blobs";

  private readonly dbRef: { promise: Promise<IDBDatabase> | null } = { promise: null };
  private readonly urls = new Map<string, string>();

  private openDB(): Promise<IDBDatabase> {
    return cachedOpen(this.dbRef, {
      name: IndexedDBBlobCache.DB_NAME,
      version: IndexedDBBlobCache.DB_VERSION,
      upgrade: (db) => {
        if (!db.objectStoreNames.contains(IndexedDBBlobCache.STORE_NAME)) {
          db.createObjectStore(IndexedDBBlobCache.STORE_NAME);
        }
      },
    });
  }

  private async getRecord(hash: string): Promise<IDBRecord | undefined> {
    const db = await this.openDB();
    const tx = db.transaction(IndexedDBBlobCache.STORE_NAME, "readonly");
    return runRequest<IDBRecord | undefined>(
      tx.objectStore(IndexedDBBlobCache.STORE_NAME).get(hash)
    );
  }

  private async putRecord(hash: string, record: IDBRecord): Promise<void> {
    const db = await this.openDB();
    await runTx(db, IndexedDBBlobCache.STORE_NAME, "readwrite", (store) => {
      store.put(record, hash);
    });
  }

  async get(hash: string): Promise<Uint8Array | undefined> {
    const record = await this.getRecord(hash);
    if (!record) return undefined;
    // Touch accessedAt to implement LRU. Fire-and-forget: the update
    // doesn't need to complete before the caller sees the bytes.
    void this.putRecord(hash, { ...record, accessedAt: Date.now() });
    return record.bytes;
  }

  async put(hash: string, bytes: Uint8Array): Promise<void> {
    const existing = await this.getRecord(hash);
    await this.putRecord(hash, {
      bytes,
      size: bytes.byteLength,
      accessedAt: Date.now(),
      pinned: existing?.pinned ?? false,
    });
  }

  async has(hash: string): Promise<boolean> {
    const db = await this.openDB();
    const tx = db.transaction(IndexedDBBlobCache.STORE_NAME, "readonly");
    const count = await runRequest(tx.objectStore(IndexedDBBlobCache.STORE_NAME).count(hash));
    return count > 0;
  }

  async delete(hash: string): Promise<void> {
    const url = this.urls.get(hash);
    if (url) {
      URL.revokeObjectURL(url);
      this.urls.delete(hash);
    }
    const db = await this.openDB();
    await runTx(db, IndexedDBBlobCache.STORE_NAME, "readwrite", (store) => {
      store.delete(hash);
    });
  }

  async pin(hash: string): Promise<void> {
    const record = await this.getRecord(hash);
    if (!record) return;
    await this.putRecord(hash, { ...record, pinned: true });
  }

  async unpin(hash: string): Promise<void> {
    const record = await this.getRecord(hash);
    if (!record) return;
    await this.putRecord(hash, { ...record, pinned: false });
  }

  async size(): Promise<number> {
    const db = await this.openDB();
    let total = 0;
    await iterateCursor<IDBRecord>(db, IndexedDBBlobCache.STORE_NAME, (_key, value) => {
      total += value.size;
    });
    return total;
  }

  async evict(maxBytes: number): Promise<number> {
    const db = await this.openDB();
    const candidates: Array<{ hash: string; accessedAt: number; size: number }> = [];
    let totalSize = 0;

    await iterateCursor<IDBRecord>(db, IndexedDBBlobCache.STORE_NAME, (key, value) => {
      totalSize += value.size;
      if (!value.pinned) {
        candidates.push({
          hash: String(key),
          accessedAt: value.accessedAt,
          size: value.size,
        });
      }
    });

    if (totalSize <= maxBytes) return 0;
    candidates.sort((a, b) => a.accessedAt - b.accessedAt);

    let freed = 0;
    for (const c of candidates) {
      if (totalSize <= maxBytes) break;
      await this.delete(c.hash);
      totalSize -= c.size;
      freed += c.size;
    }
    return freed;
  }

  async url(hash: string): Promise<string | undefined> {
    const cached = this.urls.get(hash);
    if (cached) return cached;
    const bytes = await this.get(hash);
    if (!bytes) return undefined;
    const buffer = new ArrayBuffer(bytes.byteLength);
    new Uint8Array(buffer).set(bytes);
    const objectUrl = URL.createObjectURL(new Blob([buffer]));
    this.urls.set(hash, objectUrl);
    return objectUrl;
  }

  dispose(): void {
    for (const objectUrl of this.urls.values()) {
      URL.revokeObjectURL(objectUrl);
    }
    this.urls.clear();
  }
}
