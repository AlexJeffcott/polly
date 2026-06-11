/**
 * Tests for createBlobStore — the peer-to-peer blob store that rides on a
 * MeshWebRTCAdapter's data channels.
 *
 * Two stores are wired over a pair of fake mesh adapters that route
 * sendBlobMessage from one to the other's onBlobMessage (parsing the wire
 * frame with the real serialiser), so a put on one peer and a get on the
 * other exercise the whole chunk/encrypt/announce/reassemble flow end to
 * end. The timer-driven re-request and timeout paths (5s/60s) are left to
 * the integration suite; this suite pins the deterministic request/response
 * flow, the validation guards, the cache-backed accessors, and disposal.
 */

import { afterEach, describe, expect, test } from "bun:test";
import type { BlobRef } from "@/shared/lib/blob-ref";
import { computeBlobHash } from "@/shared/lib/blob-ref";
import { createBlobStore } from "@/shared/lib/blob-store-impl";
import { parseBlobMessage } from "@/shared/lib/blob-transfer";
import { generateDocumentKey } from "@/shared/lib/encryption";
import type { MeshWebRTCAdapter } from "@/shared/lib/mesh-webrtc-adapter";

type BlobMsgHandler = (peerId: string, header: Record<string, unknown>, data: Uint8Array) => void;

/** A fake MeshWebRTCAdapter that routes blob messages to a set of wired
 * peers by re-delivering them through each peer's onBlobMessage. */
class FakeMeshAdapter {
  onBlobMessage?: BlobMsgHandler;
  private readonly peers = new Map<string, FakeMeshAdapter>();
  private readonly candidateHandlers = new Set<(e: { peerId: unknown }) => void>();

  constructor(readonly id: string) {}

  wire(other: FakeMeshAdapter): void {
    this.peers.set(other.id, other);
  }

  on(event: string, handler: (e: { peerId: unknown }) => void): void {
    if (event === "peer-candidate") this.candidateHandlers.add(handler);
  }
  off(event: string, handler: (e: { peerId: unknown }) => void): void {
    if (event === "peer-candidate") this.candidateHandlers.delete(handler);
  }

  get connectedPeerIds(): string[] {
    return [...this.peers.keys()];
  }

  sendBlobMessage(peerId: string, msg: Uint8Array): boolean {
    const target = this.peers.get(peerId);
    if (!target?.onBlobMessage) return false;
    const parsed = parseBlobMessage(msg);
    if (!parsed) return false;
    // Deliver with this adapter's id as the sender, mirroring the wire.
    target.onBlobMessage(this.id, parsed.header as unknown as Record<string, unknown>, parsed.data);
    return true;
  }

  emitPeerCandidate(peerId: string): void {
    for (const h of this.candidateHandlers) h({ peerId });
  }
}

const asAdapter = (a: FakeMeshAdapter): MeshWebRTCAdapter => a as unknown as MeshWebRTCAdapter;

async function refFor(bytes: Uint8Array): Promise<BlobRef> {
  return {
    hash: await computeBlobHash(bytes),
    size: bytes.length,
    filename: "f.bin",
    mimeType: "application/octet-stream",
  };
}

const data = (n: number, fill = 3): Uint8Array => new Uint8Array(n).fill(fill);

const stores: Array<{ dispose(): void }> = [];
afterEach(() => {
  while (stores.length) stores.pop()?.dispose();
});

/** Build two stores wired peer-to-peer. */
function buildPair(opts: { key?: Uint8Array } = {}): {
  a: ReturnType<typeof createBlobStore>;
  b: ReturnType<typeof createBlobStore>;
  adapterA: FakeMeshAdapter;
  adapterB: FakeMeshAdapter;
} {
  const adapterA = new FakeMeshAdapter("A");
  const adapterB = new FakeMeshAdapter("B");
  adapterA.wire(adapterB);
  adapterB.wire(adapterA);
  const options = opts.key ? { encrypt: { key: opts.key } } : undefined;
  const a = createBlobStore(asAdapter(adapterA), options);
  const b = createBlobStore(asAdapter(adapterB), options);
  stores.push(a, b);
  return { a, b, adapterA, adapterB };
}

describe("createBlobStore put/get round trip", () => {
  test("a put on one peer is fetched by another over the mesh", async () => {
    const { a, b } = buildPair();
    const bytes = data(200, 9);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const got = await b.get(ref.hash);
    expect(got).toBeDefined();
    expect(Array.from(got ?? [])).toEqual(Array.from(bytes));
  });

  test("round-trips an encrypted blob under a shared key", async () => {
    const key = generateDocumentKey();
    const { a, b } = buildPair({ key });
    const bytes = data(500, 7);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const got = await b.get(ref.hash);
    expect(Array.from(got ?? [])).toEqual(Array.from(bytes));
  });

  test("reassembles a multi-chunk blob larger than one chunk", async () => {
    const { a, b } = buildPair();
    // > 2 chunks (chunk size is 64 KiB).
    const bytes = data(64 * 1024 * 2 + 123, 5);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const got = await b.get(ref.hash);
    expect(got?.length).toBe(bytes.length);
    expect(Array.from(got ?? [])).toEqual(Array.from(bytes));
  });

  test("announces existing blobs to a peer that connects after the put", async () => {
    const { a, b, adapterA } = buildPair();
    const bytes = data(64, 1);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    // B has not heard the blob-have yet; a fresh peer-candidate triggers the
    // announce so B then knows A holds it and can fetch it.
    adapterA.emitPeerCandidate("B");
    const got = await b.get(ref.hash);
    expect(Array.from(got ?? [])).toEqual(Array.from(bytes));
  });
});

describe("createBlobStore get short-circuits", () => {
  test("returns from the local cache without touching the network", async () => {
    const { a } = buildPair();
    const bytes = data(64, 2);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const got = await a.get(ref.hash);
    expect(Array.from(got ?? [])).toEqual(Array.from(bytes));
  });

  test("returns undefined when no peer is known to have the blob", async () => {
    const adapter = new FakeMeshAdapter("solo");
    const store = createBlobStore(asAdapter(adapter));
    stores.push(store);
    expect(await store.get("deadbeef")).toBeUndefined();
  });
});

describe("createBlobStore validation guards", () => {
  test("rejects a put whose bytes do not match the ref hash", async () => {
    const { a } = buildPair();
    const bytes = data(32, 1);
    const ref = await refFor(bytes);
    const tampered = data(32, 2);
    await expect(a.put(ref, tampered)).rejects.toThrow("Hash mismatch");
  });

  test("rejects a put that exceeds the configured maximum size", async () => {
    const adapter = new FakeMeshAdapter("solo");
    const store = createBlobStore(asAdapter(adapter), { maxBlobSize: 16 });
    stores.push(store);
    const bytes = data(32, 1);
    const ref = await refFor(bytes);
    await expect(store.put(ref, bytes)).rejects.toThrow("exceeds maximum size");
  });
});

describe("createBlobStore cache-backed accessors", () => {
  test("url returns a stable object URL for a stored blob and undefined otherwise", async () => {
    const { a } = buildPair();
    const bytes = data(8, 4);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const first = await a.url(ref.hash);
    expect(typeof first).toBe("string");
    expect(await a.url(ref.hash)).toBe(first);
    expect(await a.url("missing")).toBeUndefined();
  });

  test("pin/unpin, size, and evict operate on the underlying cache", async () => {
    const { a } = buildPair();
    const small = data(40, 1);
    const big = data(80, 2);
    const refSmall = await refFor(small);
    const refBig = await refFor(big);
    await a.put(refSmall, small);
    await a.put(refBig, big);
    expect(await a.size()).toBe(120);
    await a.pin(refBig.hash);
    // Evict under 80: the unpinned small blob goes, the pinned big stays.
    const freed = await a.evict(80);
    expect(freed).toBe(40);
    expect(await a.size()).toBe(80);
    await a.unpin(refBig.hash);
  });
});

describe("createBlobStore disposal", () => {
  test("a disposed store rejects further put and get", async () => {
    const { a } = buildPair();
    a.dispose();
    const ref = await refFor(data(8));
    await expect(a.put(ref, data(8))).rejects.toThrow("disposed");
    await expect(a.get(ref.hash)).rejects.toThrow("disposed");
  });

  test("url returns undefined once disposed", async () => {
    const { a } = buildPair();
    const bytes = data(8, 4);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    a.dispose();
    expect(await a.url(ref.hash)).toBeUndefined();
  });
});

describe("createBlobStore progress and cancellation", () => {
  test("reports download progress to the onProgress callback", async () => {
    const { a, b } = buildPair();
    const bytes = data(64 * 1024 + 50, 6);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const events: Array<{ loaded: number; phase: string }> = [];
    await b.get(ref.hash, {
      onProgress: (p) => events.push({ loaded: p.loaded, phase: p.phase }),
    });
    expect(events.length).toBeGreaterThan(0);
    expect(events.every((e) => e.phase === "downloading")).toBe(true);
    expect(events.at(-1)?.loaded).toBeGreaterThan(0);
  });

  test("a put with an already-aborted signal throws before doing work", async () => {
    const { a } = buildPair();
    const bytes = data(16);
    const ref = await refFor(bytes);
    await expect(a.put(ref, bytes, { signal: AbortSignal.abort() })).rejects.toThrow();
  });

  test("a get with an already-aborted signal throws before requesting", async () => {
    const { a } = buildPair();
    await expect(a.get("somehash", { signal: AbortSignal.abort() })).rejects.toThrow();
  });
});

describe("createBlobStore url content", () => {
  test("the object URL resolves to the stored blob bytes", async () => {
    const { a } = buildPair();
    const bytes = data(5, 8);
    const ref = await refFor(bytes);
    await a.put(ref, bytes);
    const url = await a.url(ref.hash);
    if (!url) throw new Error("expected an object URL");
    // Fetching the URL must yield the stored bytes — a dropped `[buffer]`
    // argument would resolve to an empty payload.
    const got = new Uint8Array(await (await fetch(url)).arrayBuffer());
    expect(Array.from(got)).toEqual(Array.from(bytes));
  });
});
