/**
 * Internal-path tests for createBlobStore that the round-trip suite in
 * blob-store-impl.test.ts deliberately leaves to the integration layer:
 * the timer-driven re-request loop (5s), the download timeout (60s), the
 * multi-source peer rotation, abort handling, the decrypt-failure skip,
 * and the sender-side request handler (partial `missing` lists, out-of-range
 * indices, and the backpressure retry).
 *
 * Rather than wire two real stores end to end, these tests drive a single
 * store through a recording adapter — outgoing blob messages are captured
 * and decoded so we can assert exactly who was asked for what, and incoming
 * messages are injected by hand. Global setTimeout/clearTimeout are replaced
 * with a captured-timer shim (same approach as the mesh-signaling-client
 * reconnect tests) so the 5s/60s/50ms timers fire on demand without real
 * waits.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { computeBlobHash } from "@/shared/lib/blob-ref";
import { createBlobStore } from "@/shared/lib/blob-store-impl";
import type {
  BlobChunkHeader,
  BlobMessageHeader,
  BlobRequestHeader,
} from "@/shared/lib/blob-transfer";
import { parseBlobMessage } from "@/shared/lib/blob-transfer";
import { encrypt, generateDocumentKey } from "@/shared/lib/encryption";
import type { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

// Captured-timer shim

const realSetTimeout = globalThis.setTimeout;
const realClearTimeout = globalThis.clearTimeout;
let scheduled: Array<{ fn: () => void; delay: number; id: number }>;
let nextTimerId: number;

function installFakeTimers(): void {
  scheduled = [];
  nextTimerId = 1;
  globalThis.setTimeout = ((fn: () => void, delay?: number) => {
    const id = nextTimerId++;
    scheduled.push({ fn, delay: delay ?? 0, id });
    return id as unknown as ReturnType<typeof setTimeout>;
  }) as typeof setTimeout;
  globalThis.clearTimeout = ((id?: ReturnType<typeof setTimeout>) => {
    const i = scheduled.findIndex((s) => s.id === (id as unknown as number));
    if (i >= 0) scheduled.splice(i, 1);
  }) as typeof clearTimeout;
}

/** Fire (and remove) the earliest pending timer scheduled at `delay` ms. */
function fireTimer(delay: number): void {
  const i = scheduled.findIndex((s) => s.delay === delay);
  if (i < 0) {
    throw new Error(`no pending timer at ${delay}ms; have [${scheduled.map((s) => s.delay)}]`);
  }
  const [timer] = scheduled.splice(i, 1);
  timer?.fn();
}

/** Let queued microtasks (awaited cache reads, dynamic encryption imports,
 *  decrypts) settle before asserting. */
async function flush(): Promise<void> {
  for (let i = 0; i < 12; i++) await Promise.resolve();
}

// Recording adapter

interface SentMessage {
  peerId: string;
  header: BlobMessageHeader;
  data: Uint8Array;
}

class RecordingAdapter {
  onBlobMessage?: (peerId: string, header: Record<string, unknown>, data: Uint8Array) => void;
  readonly sent: SentMessage[] = [];
  /** When true, the next sendBlobMessage reports backpressure (returns
   *  false) and clears the flag, so the store takes the buffer-drain path. */
  failNextSend = false;
  private readonly candidateHandlers = new Set<(e: { peerId: unknown }) => void>();

  constructor(private readonly connected: string[] = []) {}

  on(event: string, handler: (e: { peerId: unknown }) => void): void {
    if (event === "peer-candidate") this.candidateHandlers.add(handler);
  }
  off(event: string, handler: (e: { peerId: unknown }) => void): void {
    if (event === "peer-candidate") this.candidateHandlers.delete(handler);
  }

  get connectedPeerIds(): string[] {
    return this.connected;
  }

  sendBlobMessage(peerId: string, msg: Uint8Array): boolean {
    if (this.failNextSend) {
      this.failNextSend = false;
      return false;
    }
    const parsed = parseBlobMessage(msg);
    if (!parsed) return false;
    this.sent.push({ peerId, header: parsed.header, data: parsed.data });
    return true;
  }

  /** Inject an incoming blob message as if it arrived from `fromPeer`. */
  deliver(fromPeer: string, header: BlobMessageHeader, data: Uint8Array = new Uint8Array(0)): void {
    this.onBlobMessage?.(fromPeer, header as unknown as Record<string, unknown>, data);
  }

  emitPeerCandidate(peerId: string): void {
    for (const h of this.candidateHandlers) h({ peerId });
  }

  /** Outgoing blob-request messages, newest last. */
  requests(): Array<{ peerId: string; header: BlobRequestHeader }> {
    return this.sent
      .filter((m) => (m.header as { type: string }).type === "blob-request")
      .map((m) => ({ peerId: m.peerId, header: m.header as BlobRequestHeader }));
  }

  /** Outgoing blob-chunk messages, newest last. */
  chunks(): Array<{ peerId: string; header: BlobChunkHeader; data: Uint8Array }> {
    return this.sent
      .filter((m) => (m.header as { type: string }).type === "blob-chunk")
      .map((m) => ({ peerId: m.peerId, header: m.header as BlobChunkHeader, data: m.data }));
  }
}

const asAdapter = (a: RecordingAdapter): MeshWebRTCAdapter => a as unknown as MeshWebRTCAdapter;

const HASH = "a".repeat(64);
const have = (hash: string): BlobMessageHeader => ({ type: "blob-have", hash });
const chunkHeader = (hash: string, index: number, total: number): BlobChunkHeader => ({
  type: "blob-chunk",
  hash,
  index,
  total,
});

const stores: Array<{ dispose(): void }> = [];

beforeEach(() => {
  installFakeTimers();
});

afterEach(() => {
  while (stores.length) stores.pop()?.dispose();
  globalThis.setTimeout = realSetTimeout;
  globalThis.clearTimeout = realClearTimeout;
});

describe("createBlobStore re-request rotation", () => {
  test("rotates through peers that announced the blob on each re-request", async () => {
    const adapter = new RecordingAdapter(["B", "C"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    // Both B and C announce availability, so the peer pool is [B, C].
    adapter.deliver("B", have(HASH));
    adapter.deliver("C", have(HASH));

    const got = store.get(HASH);
    got.catch(() => {}); // settled at the end via the timeout timer
    await flush();

    // Initial request goes to the first known holder.
    expect(adapter.requests().at(-1)?.peerId).toBe("B");

    // A partial chunk arrives, leaving chunks missing → a re-request is armed.
    adapter.deliver("B", chunkHeader(HASH, 0, 3), new Uint8Array([1]));
    await flush();

    // First re-request rotates to the next holder, C, asking for the gaps.
    fireTimer(5000);
    const afterFirst = adapter.requests().at(-1);
    expect(afterFirst?.peerId).toBe("C");
    expect(afterFirst?.header.missing).toEqual([1, 2]);

    // Second re-request wraps back to B.
    fireTimer(5000);
    expect(adapter.requests().at(-1)?.peerId).toBe("B");

    // Settle the still-pending get so no timer leaks past the test.
    fireTimer(60000);
    await expect(got).rejects.toThrow(/timed out/);
  });

  test("falls back to connected peers when no holder has announced", async () => {
    const adapter = new RecordingAdapter(["P"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    // No blob-have was received, so peerBlobs is empty; the store must use
    // the connected peer list both for the initial request and re-requests.
    const got = store.get(HASH);
    got.catch(() => {});
    await flush();
    expect(adapter.requests().at(-1)?.peerId).toBe("P");

    adapter.deliver("P", chunkHeader(HASH, 0, 2), new Uint8Array([7]));
    await flush();
    fireTimer(5000);
    expect(adapter.requests().at(-1)?.peerId).toBe("P");

    fireTimer(60000);
    await expect(got).rejects.toThrow(/timed out/);
  });
});

describe("createBlobStore download lifecycle", () => {
  test("rejects with a timeout when no chunks complete the blob", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    const got = store.get(HASH);
    await flush();
    fireTimer(60000);
    await expect(got).rejects.toThrow("Blob download timed out");
  });

  test("rejects when the caller aborts mid-download", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    const controller = new AbortController();
    const got = store.get(HASH, { signal: controller.signal });
    await flush();
    controller.abort();
    await expect(got).rejects.toThrow("Blob download aborted");
  });

  test("reports cumulative download progress as chunks arrive", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    const loaded: number[] = [];
    const got = store.get(HASH, { onProgress: (p) => loaded.push(p.loaded) });
    got.catch(() => {});
    await flush();

    adapter.deliver("B", chunkHeader(HASH, 0, 3), new Uint8Array([1, 2]));
    await flush();
    adapter.deliver("B", chunkHeader(HASH, 1, 3), new Uint8Array([3, 4, 5]));
    await flush();

    // Progress accumulates the byte lengths of decrypted chunks: 2 then 2+3.
    expect(loaded).toEqual([2, 5]);

    fireTimer(60000);
    await expect(got).rejects.toThrow(/timed out/);
  });
});

describe("createBlobStore chunk decryption", () => {
  test("skips an undecryptable chunk and completes from a valid one", async () => {
    const key = generateDocumentKey();
    const plaintext = new Uint8Array([10, 20, 30, 40]);
    const hash = await computeBlobHash(plaintext);

    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter), { encrypt: { key } });
    stores.push(store);

    const got = store.get(hash);
    got.catch(() => {});
    await flush();

    // Garbage that fails authentication must be dropped, not folded into the
    // assembled blob — otherwise reassembly would corrupt or reject.
    adapter.deliver("B", chunkHeader(hash, 0, 1), new Uint8Array([9, 9, 9, 9, 9, 9]));
    await flush();

    // The genuine sealed chunk decrypts and completes the single-chunk blob.
    const sealed = encrypt(plaintext, key);
    adapter.deliver("B", chunkHeader(hash, 0, 1), sealed);

    const result = await got;
    expect(Array.from(result as Uint8Array)).toEqual(Array.from(plaintext));
  });
});

describe("createBlobStore request handler (sender side)", () => {
  async function seed(adapter: RecordingAdapter, bytes: Uint8Array): Promise<string> {
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);
    const hash = await computeBlobHash(bytes);
    await store.put(
      { hash, size: bytes.length, filename: "f", mimeType: "application/octet-stream" },
      bytes
    );
    // The put announced a blob-have to connected peers; drop it so request
    // assertions only see chunk traffic.
    adapter.sent.length = 0;
    return hash;
  }

  test("serves only the requested chunk indices when 'missing' is given", async () => {
    const adapter = new RecordingAdapter(["B"]);
    // Two chunks: 64 KiB + a tail byte.
    const bytes = new Uint8Array(65_536 + 1).fill(4);
    const hash = await seed(adapter, bytes);

    adapter.deliver("B", { type: "blob-request", hash, missing: [1] } as BlobMessageHeader);
    await flush();

    const served = adapter.chunks();
    expect(served).toHaveLength(1);
    expect(served[0]?.header.index).toBe(1);
    expect(served[0]?.peerId).toBe("B");
  });

  test("ignores requested indices that are out of range", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const bytes = new Uint8Array(32).fill(1);
    const hash = await seed(adapter, bytes);

    adapter.deliver("B", { type: "blob-request", hash, missing: [99] } as BlobMessageHeader);
    await flush();

    expect(adapter.chunks()).toHaveLength(0);
  });

  test("serves every chunk when no 'missing' list is provided", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const bytes = new Uint8Array(65_536 + 10).fill(2);
    const hash = await seed(adapter, bytes);

    adapter.deliver("B", { type: "blob-request", hash } as BlobMessageHeader);
    await flush();

    const indices = adapter.chunks().map((c) => c.header.index);
    expect(indices).toEqual([0, 1]);
  });

  test("retries a chunk send after backpressure drains", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const bytes = new Uint8Array(16).fill(5);
    const hash = await seed(adapter, bytes);

    // First send reports the channel buffer is full.
    adapter.failNextSend = true;
    adapter.deliver("B", { type: "blob-request", hash } as BlobMessageHeader);
    await flush();
    // Nothing sent yet — the handler is parked on waitForBufferDrain.
    expect(adapter.chunks()).toHaveLength(0);

    // Drain the 50ms backpressure timer; the chunk is then resent.
    fireTimer(50);
    await flush();
    expect(adapter.chunks()).toHaveLength(1);
    expect(adapter.chunks()[0]?.header.index).toBe(0);
  });
});

describe("createBlobStore have-announcement on peer connect", () => {
  test("announces every locally held blob to a peer that connects later", async () => {
    const adapter = new RecordingAdapter([]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    const bytes = new Uint8Array(8).fill(3);
    const hash = await computeBlobHash(bytes);
    await store.put(
      { hash, size: bytes.length, filename: "f", mimeType: "application/octet-stream" },
      bytes
    );
    adapter.sent.length = 0;

    adapter.emitPeerCandidate("late");
    await flush();

    const announced = adapter.sent.filter(
      (m) => (m.header as { type: string }).type === "blob-have"
    );
    expect(announced).toHaveLength(1);
    expect(announced[0]?.peerId).toBe("late");
    expect((announced[0]?.header as { hash: string }).hash).toBe(hash);
  });
});

describe("createBlobStore download integrity", () => {
  test("rejects a completed download whose bytes do not match the requested hash", async () => {
    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    // HASH is a fixed dummy; the delivered bytes hash to something else, so a
    // single chunk "completes" the transfer with content that fails the
    // post-download integrity check.
    const got = store.get(HASH);
    got.catch(() => {});
    await flush(); // let the download register before chunks arrive
    adapter.deliver("B", chunkHeader(HASH, 0, 1), new Uint8Array([1, 2, 3, 4]));
    await expect(got).rejects.toThrow(/hash mismatch after download/i);
  });
});

describe("createBlobStore size guard boundary", () => {
  test("accepts a blob whose size is exactly the maximum", async () => {
    const adapter = new RecordingAdapter([]);
    const store = createBlobStore(asAdapter(adapter), { maxBlobSize: 32 });
    stores.push(store);

    // The guard rejects only when bytes exceed the max; a blob exactly at the
    // limit must be stored. Pins `>` against a `>=` off-by-one.
    const bytes = new Uint8Array(32).fill(1);
    const hash = await computeBlobHash(bytes);
    await store.put(
      { hash, size: bytes.length, filename: "f", mimeType: "application/octet-stream" },
      bytes
    );
    expect(await store.size()).toBe(32);
  });
});

describe("createBlobStore pinning", () => {
  test("unpinning a blob makes it evictable again", async () => {
    const adapter = new RecordingAdapter([]);
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);

    const bytes = new Uint8Array(40).fill(1);
    const hash = await computeBlobHash(bytes);
    await store.put(
      { hash, size: bytes.length, filename: "f", mimeType: "application/octet-stream" },
      bytes
    );

    await store.pin(hash);
    // Pinned: an aggressive evict cannot reclaim it.
    expect(await store.evict(0)).toBe(0);

    await store.unpin(hash);
    // Unpinned: the same evict now frees its bytes.
    expect(await store.evict(0)).toBe(40);
  });
});

describe("createBlobStore disposal cleanup", () => {
  test("dispose revokes every object URL it handed out", async () => {
    const revoked: string[] = [];
    const realRevoke = URL.revokeObjectURL;
    URL.revokeObjectURL = (u: string) => {
      revoked.push(u);
    };
    try {
      const adapter = new RecordingAdapter([]);
      const store = createBlobStore(asAdapter(adapter));
      const bytes = new Uint8Array(8).fill(2);
      const hash = await computeBlobHash(bytes);
      await store.put(
        { hash, size: bytes.length, filename: "f", mimeType: "application/octet-stream" },
        bytes
      );
      const url = await store.url(hash);
      if (!url) throw new Error("expected an object URL");

      store.dispose();
      expect(revoked).toContain(url);
    } finally {
      URL.revokeObjectURL = realRevoke;
    }
  });
});

describe("createBlobStore key retention", () => {
  test("re-serves a fetched encrypted blob to a peer under the same key", async () => {
    const key = generateDocumentKey();
    const plaintext = new Uint8Array([5, 6, 7, 8]);
    const hash = await computeBlobHash(plaintext);

    const adapter = new RecordingAdapter(["B"]);
    const store = createBlobStore(asAdapter(adapter), { encrypt: { key } });
    stores.push(store);

    // Fetch the blob: completing the download must record the key under its
    // hash so the store can later re-encrypt when another peer asks for it.
    const got = store.get(hash);
    got.catch(() => {});
    await flush();
    adapter.deliver("B", chunkHeader(hash, 0, 1), encrypt(plaintext, key));
    expect(Array.from((await got) as Uint8Array)).toEqual(Array.from(plaintext));

    // A new peer requests the blob. The served chunk must be ciphertext that
    // decrypts back to the plaintext — not the raw plaintext.
    adapter.sent.length = 0;
    adapter.deliver("C", { type: "blob-request", hash } as BlobMessageHeader);
    await flush();

    const served = adapter.chunks();
    expect(served).toHaveLength(1);
    const sealed = served[0]?.data;
    if (!sealed) throw new Error("expected a served chunk");
    const { decrypt } = await import("@/shared/lib/encryption");
    const opened = decrypt(sealed, key);
    if (!opened) throw new Error("served chunk did not decrypt under the key");
    expect(Array.from(opened)).toEqual(Array.from(plaintext));
  });
});
