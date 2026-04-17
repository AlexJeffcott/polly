import { describe, expect, test } from "bun:test";
import { MemoryBlobCache } from "@/shared/lib/blob-cache";
import { computeBlobHash, createBlobRef } from "@/shared/lib/blob-ref";
import type { BlobProgressEvent } from "@/shared/lib/blob-store";
import { createBlobStore } from "@/shared/lib/blob-store-impl";
import {
  type BlobChunkHeader,
  type BlobRequestHeader,
  chunkBlob,
} from "@/shared/lib/blob-transfer";
import { decrypt, encrypt, generateDocumentKey } from "@/shared/lib/encryption";

// ---------------------------------------------------------------------------
// Mock MeshWebRTCAdapter
// ---------------------------------------------------------------------------

type BlobHandler = (peerId: string, header: Record<string, unknown>, data: Uint8Array) => void;
type PeerCandidateHandler = (event: { peerId: unknown }) => void;

function createMockAdapter(initialPeers: string[] = ["peer-a", "peer-b"]) {
  const sentMessages: Array<{ peerId: string; bytes: Uint8Array }> = [];
  let blobHandler: BlobHandler | undefined;
  const eventHandlers = new Map<string, Set<PeerCandidateHandler>>();
  let connectedPeers = [...initialPeers];

  return {
    get onBlobMessage() {
      return blobHandler;
    },
    set onBlobMessage(fn: BlobHandler | undefined) {
      blobHandler = fn;
    },
    get connectedPeerIds(): string[] {
      return connectedPeers;
    },
    sendBlobMessage(peerId: string, bytes: Uint8Array<ArrayBuffer>): boolean {
      sentMessages.push({ peerId, bytes });
      return true;
    },
    on(event: string, handler: PeerCandidateHandler) {
      let handlers = eventHandlers.get(event);
      if (!handlers) {
        handlers = new Set();
        eventHandlers.set(event, handlers);
      }
      handlers.add(handler);
    },
    off(event: string, handler: PeerCandidateHandler) {
      eventHandlers.get(event)?.delete(handler);
    },
    sentMessages,
    simulateIncoming(peerId: string, header: Record<string, unknown>, data: Uint8Array) {
      blobHandler?.(peerId, header, data);
    },
    simulatePeerConnect(peerId: string) {
      connectedPeers.push(peerId);
      const handlers = eventHandlers.get("peer-candidate");
      if (handlers) {
        for (const handler of handlers) handler({ peerId });
      }
    },
    setConnectedPeers(peers: string[]) {
      connectedPeers = peers;
    },
  };
}

// ---------------------------------------------------------------------------
// MemoryBlobCache
// ---------------------------------------------------------------------------

describe("MemoryBlobCache", () => {
  test("put and get round-trip", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("abc", new Uint8Array([1, 2, 3]));
    expect(await cache.get("abc")).toEqual(new Uint8Array([1, 2, 3]));
  });

  test("has returns correct values", async () => {
    const cache = new MemoryBlobCache();
    expect(await cache.has("x")).toBe(false);
    await cache.put("x", new Uint8Array(1));
    expect(await cache.has("x")).toBe(true);
  });

  test("delete removes entry", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("x", new Uint8Array(1));
    await cache.delete("x");
    expect(await cache.has("x")).toBe(false);
  });

  test("size returns total bytes stored", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(10));
    await cache.put("b", new Uint8Array(20));
    expect(await cache.size()).toBe(30);
  });

  test("evict removes LRU entries until under maxBytes", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(100));
    // Force different access times.
    await new Promise((r) => setTimeout(r, 2));
    await cache.put("b", new Uint8Array(100));
    await new Promise((r) => setTimeout(r, 2));
    await cache.put("c", new Uint8Array(100));
    // Now 300 bytes. Evict to 150.
    const freed = await cache.evict(150);
    expect(freed).toBeGreaterThanOrEqual(100);
    expect(await cache.has("a")).toBe(false); // oldest evicted
    expect(await cache.has("c")).toBe(true); // newest retained
  });

  test("evict skips pinned entries", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(100));
    await cache.pin("a");
    await new Promise((r) => setTimeout(r, 2));
    await cache.put("b", new Uint8Array(100));
    await cache.evict(50);
    // "a" is pinned and should survive even though it's older.
    expect(await cache.has("a")).toBe(true);
    expect(await cache.has("b")).toBe(false);
  });

  test("unpin makes a blob eligible for eviction again", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(100));
    await cache.pin("a");
    await cache.unpin("a");
    await cache.evict(50);
    expect(await cache.has("a")).toBe(false);
  });

  test("evict returns 0 when under maxBytes already", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(50));
    expect(await cache.evict(100)).toBe(0);
  });

  test("get updates access time (LRU recency)", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(100));
    await new Promise((r) => setTimeout(r, 2));
    await cache.put("b", new Uint8Array(100));
    await new Promise((r) => setTimeout(r, 2));
    // Access "a" — now "b" becomes the LRU.
    await cache.get("a");
    await cache.evict(150);
    expect(await cache.has("a")).toBe(true);
    expect(await cache.has("b")).toBe(false);
  });

  test("dispose clears all entries and pins", async () => {
    const cache = new MemoryBlobCache();
    await cache.put("a", new Uint8Array(1));
    await cache.pin("a");
    cache.dispose();
    expect(await cache.has("a")).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// createBlobStore — core operations
// ---------------------------------------------------------------------------

describe("createBlobStore — core", () => {
  test("put stores blob and announces to peers", async () => {
    const cache = new MemoryBlobCache();
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never, { cache });

    const bytes = new TextEncoder().encode("hello blob");
    const ref = await createBlobRef({ bytes, filename: "test.txt", mimeType: "text/plain" });

    await store.put(ref, bytes);

    expect(await cache.has(ref.hash)).toBe(true);
    const haveMessages = adapter.sentMessages.filter((m) => {
      const text = new TextDecoder().decode(m.bytes.subarray(4));
      return text.includes('"blob-have"');
    });
    expect(haveMessages.length).toBeGreaterThanOrEqual(2);
  });

  test("put rejects when hash does not match", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const ref = { hash: "0".repeat(64), size: 5, filename: "bad", mimeType: "text/plain" };
    await expect(store.put(ref, new TextEncoder().encode("hello"))).rejects.toThrow(
      "Hash mismatch"
    );
  });

  test("put rejects blobs exceeding maxBlobSize", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never, { maxBlobSize: 10 });
    const bytes = new Uint8Array(11);
    const ref = await createBlobRef({
      bytes,
      filename: "big",
      mimeType: "application/octet-stream",
    });
    await expect(store.put(ref, bytes)).rejects.toThrow("exceeds maximum size");
  });

  test("get returns cached blob without network", async () => {
    const cache = new MemoryBlobCache();
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never, { cache });
    const bytes = new TextEncoder().encode("cached data");
    const ref = await createBlobRef({ bytes, filename: "c", mimeType: "text/plain" });
    await store.put(ref, bytes);
    const result = await store.get(ref.hash);
    expect(result).toEqual(bytes);
    const requests = adapter.sentMessages.filter((m) =>
      new TextDecoder().decode(m.bytes.subarray(4)).includes('"blob-request"')
    );
    expect(requests).toHaveLength(0);
  });

  test("handles blob-request by sending chunks", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = new TextEncoder().encode("share me");
    const ref = await createBlobRef({ bytes, filename: "s", mimeType: "text/plain" });
    await store.put(ref, bytes);
    adapter.sentMessages.length = 0;

    const requestHeader: BlobRequestHeader = { type: "blob-request", hash: ref.hash };
    adapter.simulateIncoming(
      "peer-a",
      requestHeader as unknown as Record<string, unknown>,
      new Uint8Array(0)
    );
    await new Promise((r) => setTimeout(r, 10));
    expect(adapter.sentMessages.length).toBeGreaterThan(0);
    expect(adapter.sentMessages[0]!.peerId).toBe("peer-a");
  });

  test("get downloads plaintext chunks and reassembles", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = new TextEncoder().encode("download me");
    const hash = await computeBlobHash(bytes);

    const getPromise = store.get(hash);
    await new Promise((r) => setTimeout(r, 10));

    const chunks = chunkBlob(bytes);
    for (let i = 0; i < chunks.length; i++) {
      const header: BlobChunkHeader = { type: "blob-chunk", hash, index: i, total: chunks.length };
      adapter.simulateIncoming("peer-a", header as unknown as Record<string, unknown>, chunks[i]!);
    }

    const result = await getPromise;
    expect(result).toEqual(bytes);
  });

  test("dispose rejects pending downloads", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const hash = "f".repeat(64);
    adapter.simulateIncoming("peer-a", { type: "blob-have", hash }, new Uint8Array(0));
    const getPromise = store.get(hash);
    await new Promise((r) => setTimeout(r, 10));
    store.dispose();
    await expect(getPromise).rejects.toThrow("disposed");
  });

  test("put supports AbortSignal", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const controller = new AbortController();
    controller.abort();
    const bytes = new TextEncoder().encode("abort me");
    const ref = await createBlobRef({ bytes, filename: "a", mimeType: "text/plain" });
    await expect(store.put(ref, bytes, { signal: controller.signal })).rejects.toThrow();
  });
});

// ---------------------------------------------------------------------------
// Chunk-then-encrypt (streaming encryption)
// ---------------------------------------------------------------------------

describe("chunk-then-encrypt", () => {
  test("put stores plaintext; handleRequest encrypts chunks individually", async () => {
    const adapter = createMockAdapter();
    const docKey = generateDocumentKey();
    const cache = new MemoryBlobCache();
    const store = createBlobStore(adapter as unknown as never, {
      cache,
      encrypt: { key: docKey },
    });

    const bytes = new TextEncoder().encode("streaming encryption test");
    const ref = await createBlobRef({ bytes, filename: "e", mimeType: "text/plain" });
    await store.put(ref, bytes);

    // Cache stores plaintext (not ciphertext) for streaming on request.
    expect(await cache.get(ref.hash)).toEqual(bytes);

    // Trigger a request from a peer and check each emitted chunk is an
    // independently-sealed envelope (nonce + ciphertext + MAC).
    adapter.sentMessages.length = 0;
    adapter.simulateIncoming(
      "peer-a",
      { type: "blob-request", hash: ref.hash } as unknown as Record<string, unknown>,
      new Uint8Array(0)
    );
    await new Promise((r) => setTimeout(r, 20));

    const chunkMsgs = adapter.sentMessages.filter((m) =>
      new TextDecoder().decode(m.bytes.subarray(4)).includes('"blob-chunk"')
    );
    expect(chunkMsgs.length).toBeGreaterThan(0);

    // Decode each chunk's payload and verify it decrypts independently.
    for (const msg of chunkMsgs) {
      const view = new DataView(msg.bytes.buffer, msg.bytes.byteOffset, msg.bytes.byteLength);
      const headerLen = view.getUint32(0, false);
      const payload = msg.bytes.subarray(4 + headerLen);
      const plain = decrypt(payload, docKey);
      expect(plain).toBeDefined();
    }
  });

  test("get decrypts chunks received from peer", async () => {
    const adapter = createMockAdapter();
    const docKey = generateDocumentKey();
    const store = createBlobStore(adapter as unknown as never, { encrypt: { key: docKey } });

    const bytes = new TextEncoder().encode("decrypt me");
    const hash = await computeBlobHash(bytes);

    const getPromise = store.get(hash);
    await new Promise((r) => setTimeout(r, 10));

    const plainChunks = chunkBlob(bytes);
    for (let i = 0; i < plainChunks.length; i++) {
      const sealed = encrypt(plainChunks[i]!, docKey);
      const header: BlobChunkHeader = {
        type: "blob-chunk",
        hash,
        index: i,
        total: plainChunks.length,
      };
      adapter.simulateIncoming("peer-a", header as unknown as Record<string, unknown>, sealed);
    }

    const result = await getPromise;
    expect(result).toEqual(bytes);
  });

  test("wrong key: decryption silently drops chunks, download times out", async () => {
    const adapter = createMockAdapter();
    const correctKey = generateDocumentKey();
    const wrongKey = generateDocumentKey();
    const store = createBlobStore(adapter as unknown as never, {
      encrypt: { key: wrongKey },
    });

    const bytes = new TextEncoder().encode("mismatched keys");
    const hash = await computeBlobHash(bytes);

    // Disable the 60s timeout by not waiting that long — instead, observe
    // that chunks fail to decrypt and are dropped.
    const getPromise = store.get(hash);
    await new Promise((r) => setTimeout(r, 10));

    const plainChunks = chunkBlob(bytes);
    for (let i = 0; i < plainChunks.length; i++) {
      const sealed = encrypt(plainChunks[i]!, correctKey);
      const header: BlobChunkHeader = {
        type: "blob-chunk",
        hash,
        index: i,
        total: plainChunks.length,
      };
      adapter.simulateIncoming("peer-a", header as unknown as Record<string, unknown>, sealed);
    }

    // Wait long enough for chunks to be dropped, then abort to avoid waiting 60s.
    await new Promise((r) => setTimeout(r, 50));
    // The download never completed because all chunks were dropped.
    // Force a timeout by disposing.
    store.dispose();
    await expect(getPromise).rejects.toThrow();
  });
});

// ---------------------------------------------------------------------------
// Per-document keys (per-op key override)
// ---------------------------------------------------------------------------

describe("per-document keys", () => {
  test("put with per-op key encrypts under that key, not the store default", async () => {
    const adapter = createMockAdapter();
    const defaultKey = generateDocumentKey();
    const docKey = generateDocumentKey();
    const store = createBlobStore(adapter as unknown as never, { encrypt: { key: defaultKey } });

    const bytes = new TextEncoder().encode("doc-scoped blob");
    const ref = await createBlobRef({ bytes, filename: "d", mimeType: "text/plain" });
    await store.put(ref, bytes, { key: docKey });

    adapter.sentMessages.length = 0;
    adapter.simulateIncoming(
      "peer-a",
      { type: "blob-request", hash: ref.hash } as unknown as Record<string, unknown>,
      new Uint8Array(0)
    );
    await new Promise((r) => setTimeout(r, 20));

    const chunkMsgs = adapter.sentMessages.filter((m) =>
      new TextDecoder().decode(m.bytes.subarray(4)).includes('"blob-chunk"')
    );
    expect(chunkMsgs.length).toBeGreaterThan(0);

    // Decrypt with docKey should succeed; with defaultKey should fail.
    for (const msg of chunkMsgs) {
      const view = new DataView(msg.bytes.buffer, msg.bytes.byteOffset, msg.bytes.byteLength);
      const headerLen = view.getUint32(0, false);
      const payload = msg.bytes.subarray(4 + headerLen);
      expect(decrypt(payload, docKey)).toBeDefined();
      expect(decrypt(payload, defaultKey)).toBeUndefined();
    }
  });

  test("get with per-op key decrypts under that key", async () => {
    const adapter = createMockAdapter();
    const docKey = generateDocumentKey();
    const store = createBlobStore(adapter as unknown as never);

    const bytes = new TextEncoder().encode("per-op key test");
    const hash = await computeBlobHash(bytes);

    const getPromise = store.get(hash, { key: docKey });
    await new Promise((r) => setTimeout(r, 10));

    const plainChunks = chunkBlob(bytes);
    for (let i = 0; i < plainChunks.length; i++) {
      const sealed = encrypt(plainChunks[i]!, docKey);
      const header: BlobChunkHeader = {
        type: "blob-chunk",
        hash,
        index: i,
        total: plainChunks.length,
      };
      adapter.simulateIncoming("peer-a", header as unknown as Record<string, unknown>, sealed);
    }

    const result = await getPromise;
    expect(result).toEqual(bytes);
  });
});

// ---------------------------------------------------------------------------
// Multi-source parallel fetch
// ---------------------------------------------------------------------------

describe("multi-source fetch", () => {
  test("re-request rotates to a different peer when chunks stall", async () => {
    const adapter = createMockAdapter(["peer-a", "peer-b", "peer-c"]);
    const store = createBlobStore(adapter as unknown as never);

    // Multiple peers announce availability.
    const hash = "a".repeat(64);
    adapter.simulateIncoming("peer-a", { type: "blob-have", hash }, new Uint8Array(0));
    adapter.simulateIncoming("peer-b", { type: "blob-have", hash }, new Uint8Array(0));
    adapter.simulateIncoming("peer-c", { type: "blob-have", hash }, new Uint8Array(0));

    const getPromise = store.get(hash);
    await new Promise((r) => setTimeout(r, 10));

    // Send chunk 0 only (of 2). The download won't complete.
    const bytes = new Uint8Array(100_000); // spans multiple chunks
    crypto.getRandomValues(bytes);
    const plainChunks = chunkBlob(bytes);
    const header0: BlobChunkHeader = {
      type: "blob-chunk",
      hash,
      index: 0,
      total: plainChunks.length,
    };
    adapter.simulateIncoming(
      "peer-a",
      header0 as unknown as Record<string, unknown>,
      plainChunks[0]!
    );

    adapter.sentMessages.length = 0;
    // Wait for re-request timer (5s).
    await new Promise((r) => setTimeout(r, 5200));

    // Should have re-requested from a peer other than "peer-a" (rotation).
    const reRequests = adapter.sentMessages.filter((m) =>
      new TextDecoder().decode(m.bytes.subarray(4)).includes('"blob-request"')
    );
    expect(reRequests.length).toBeGreaterThan(0);
    const firstRetryPeer = reRequests[0]!.peerId;
    expect(["peer-b", "peer-c"]).toContain(firstRetryPeer);

    // Clean up the pending promise.
    store.dispose();
    await expect(getPromise).rejects.toThrow();
  }, 15_000);
});

// ---------------------------------------------------------------------------
// Cache eviction via store
// ---------------------------------------------------------------------------

describe("store eviction", () => {
  test("pin/unpin/evict flow through the store API", async () => {
    const cache = new MemoryBlobCache();
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never, { cache });

    const a = new Uint8Array(100);
    const b = new Uint8Array(100);
    b.fill(1); // distinct content => distinct hash
    const refA = await createBlobRef({ bytes: a, filename: "a", mimeType: "x" });
    const refB = await createBlobRef({ bytes: b, filename: "b", mimeType: "x" });

    await store.put(refA, a);
    await store.pin(refA.hash);
    await new Promise((r) => setTimeout(r, 2));
    await store.put(refB, b);

    expect(await store.size()).toBe(200);

    await store.evict(50);
    expect(await cache.has(refA.hash)).toBe(true); // pinned
    expect(await cache.has(refB.hash)).toBe(false); // evicted
  });
});

// ---------------------------------------------------------------------------
// Progress & announcements (carried forward)
// ---------------------------------------------------------------------------

describe("progress callbacks", () => {
  test("put fires uploading progress", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = new TextEncoder().encode("progress test");
    const ref = await createBlobRef({ bytes, filename: "p", mimeType: "text/plain" });
    const events: BlobProgressEvent[] = [];
    await store.put(ref, bytes, { onProgress: (e) => events.push({ ...e }) });
    expect(events.some((e) => e.phase === "uploading")).toBe(true);
  });

  test("get fires downloading progress during chunk reception", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = crypto.getRandomValues(new Uint8Array(65_536 * 3 + 100));
    const hash = await computeBlobHash(bytes);
    const events: BlobProgressEvent[] = [];
    const getPromise = store.get(hash, { onProgress: (e) => events.push({ ...e }) });
    await new Promise((r) => setTimeout(r, 10));
    const chunks = chunkBlob(bytes);
    for (let i = 0; i < chunks.length; i++) {
      const header: BlobChunkHeader = { type: "blob-chunk", hash, index: i, total: chunks.length };
      adapter.simulateIncoming("peer-a", header as unknown as Record<string, unknown>, chunks[i]!);
    }
    await getPromise;
    const downloadEvents = events.filter((e) => e.phase === "downloading");
    expect(downloadEvents.length).toBeGreaterThan(0);
  });
});

describe("peer-connect announcements", () => {
  test("announces local blobs to newly connected peers", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = new TextEncoder().encode("announce me");
    const ref = await createBlobRef({ bytes, filename: "a", mimeType: "text/plain" });
    await store.put(ref, bytes);
    adapter.sentMessages.length = 0;
    adapter.simulatePeerConnect("peer-c");
    const haves = adapter.sentMessages.filter(
      (m) =>
        m.peerId === "peer-c" &&
        new TextDecoder().decode(m.bytes.subarray(4)).includes('"blob-have"')
    );
    expect(haves).toHaveLength(1);
  });

  test("dispose stops announcing to new peers", async () => {
    const adapter = createMockAdapter();
    const store = createBlobStore(adapter as unknown as never);
    const bytes = new TextEncoder().encode("disposed");
    const ref = await createBlobRef({ bytes, filename: "d", mimeType: "text/plain" });
    await store.put(ref, bytes);
    store.dispose();
    adapter.sentMessages.length = 0;
    adapter.simulatePeerConnect("peer-d");
    expect(adapter.sentMessages).toHaveLength(0);
  });
});
