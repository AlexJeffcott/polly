import { describe, expect, test } from "bun:test";
import {
  BLOB_CHUNK_SIZE,
  chunkBlob,
  missingChunkIndices,
  parseBlobMessage,
  reassembleChunks,
  serialiseBlobMessage,
} from "@/shared/lib/blob-transfer";

describe("chunkBlob", () => {
  test("returns a single chunk for data smaller than chunk size", () => {
    const bytes = new Uint8Array([1, 2, 3]);
    const chunks = chunkBlob(bytes, 64);
    expect(chunks).toHaveLength(1);
    expect(chunks[0]).toEqual(new Uint8Array([1, 2, 3]));
  });

  test("splits data into correct number of chunks", () => {
    const bytes = new Uint8Array(200);
    const chunks = chunkBlob(bytes, 64);
    expect(chunks).toHaveLength(4); // 64+64+64+8
    expect(chunks[0]).toHaveLength(64);
    expect(chunks[1]).toHaveLength(64);
    expect(chunks[2]).toHaveLength(64);
    expect(chunks[3]).toHaveLength(8);
  });

  test("handles exact multiple of chunk size", () => {
    const bytes = new Uint8Array(128);
    const chunks = chunkBlob(bytes, 64);
    expect(chunks).toHaveLength(2);
    expect(chunks[0]).toHaveLength(64);
    expect(chunks[1]).toHaveLength(64);
  });

  test("produces one empty chunk for empty input", () => {
    const chunks = chunkBlob(new Uint8Array(0));
    expect(chunks).toHaveLength(1);
    expect(chunks[0]).toHaveLength(0);
  });

  test("uses default chunk size of 64 KiB", () => {
    const bytes = new Uint8Array(BLOB_CHUNK_SIZE + 1);
    const chunks = chunkBlob(bytes);
    expect(chunks).toHaveLength(2);
    expect(chunks[0]).toHaveLength(BLOB_CHUNK_SIZE);
    expect(chunks[1]).toHaveLength(1);
  });
});

describe("reassembleChunks", () => {
  test("reassembles chunks in order", () => {
    const original = new Uint8Array([1, 2, 3, 4, 5]);
    const chunks = chunkBlob(original, 2);
    const map = new Map<number, Uint8Array>();
    for (let i = 0; i < chunks.length; i++) {
      map.set(i, chunks[i]!);
    }
    const result = reassembleChunks(map, chunks.length);
    expect(result).toEqual(original);
  });

  test("reassembles chunks added out of order", () => {
    const original = new Uint8Array([10, 20, 30, 40, 50, 60]);
    const chunks = chunkBlob(original, 2);
    const map = new Map<number, Uint8Array>();
    // Add in reverse order.
    for (let i = chunks.length - 1; i >= 0; i--) {
      map.set(i, chunks[i]!);
    }
    const result = reassembleChunks(map, chunks.length);
    expect(result).toEqual(original);
  });

  test("throws when a chunk is missing", () => {
    const map = new Map<number, Uint8Array>();
    map.set(0, new Uint8Array([1]));
    // Chunk 1 is missing.
    map.set(2, new Uint8Array([3]));
    expect(() => reassembleChunks(map, 3)).toThrow("missing chunk 1");
  });

  test("round-trips through chunk and reassemble for large data", () => {
    const original = crypto.getRandomValues(new Uint8Array(200_000));
    const chunks = chunkBlob(original);
    const map = new Map<number, Uint8Array>();
    for (let i = 0; i < chunks.length; i++) {
      map.set(i, chunks[i]!);
    }
    const result = reassembleChunks(map, chunks.length);
    expect(result).toEqual(original);
  });
});

describe("missingChunkIndices", () => {
  test("returns all indices when map is empty", () => {
    const missing = missingChunkIndices(new Map(), 3);
    expect(missing).toEqual([0, 1, 2]);
  });

  test("returns empty array when all chunks present", () => {
    const map = new Map<number, Uint8Array>();
    map.set(0, new Uint8Array(1));
    map.set(1, new Uint8Array(1));
    const missing = missingChunkIndices(map, 2);
    expect(missing).toEqual([]);
  });

  test("returns only missing indices", () => {
    const map = new Map<number, Uint8Array>();
    map.set(0, new Uint8Array(1));
    map.set(2, new Uint8Array(1));
    const missing = missingChunkIndices(map, 4);
    expect(missing).toEqual([1, 3]);
  });
});

describe("serialiseBlobMessage / parseBlobMessage", () => {
  test("round-trips a blob-chunk message", () => {
    const header = { type: "blob-chunk" as const, hash: "a".repeat(64), index: 3, total: 10 };
    const data = new Uint8Array([0xde, 0xad, 0xbe, 0xef]);
    const bytes = serialiseBlobMessage(header, data);
    const parsed = parseBlobMessage(bytes);
    expect(parsed).toBeDefined();
    expect(parsed!.header).toEqual(header);
    expect(parsed!.data).toEqual(data);
  });

  test("round-trips a blob-request message with no data", () => {
    const header = { type: "blob-request" as const, hash: "b".repeat(64), missing: [1, 5] };
    const bytes = serialiseBlobMessage(header);
    const parsed = parseBlobMessage(bytes);
    expect(parsed).toBeDefined();
    expect(parsed!.header).toEqual(header);
    expect(parsed!.data).toHaveLength(0);
  });

  test("round-trips a blob-have message", () => {
    const header = { type: "blob-have" as const, hash: "c".repeat(64) };
    const bytes = serialiseBlobMessage(header);
    const parsed = parseBlobMessage(bytes);
    expect(parsed).toBeDefined();
    expect(parsed!.header).toEqual(header);
  });

  test("returns undefined for truncated bytes", () => {
    expect(parseBlobMessage(new Uint8Array([1, 2]))).toBeUndefined();
  });

  test("returns undefined for invalid JSON", () => {
    const buffer = new ArrayBuffer(8);
    const view = new DataView(buffer);
    view.setUint32(0, 4, false);
    new Uint8Array(buffer).set([0xff, 0xff, 0xff, 0xff], 4);
    expect(parseBlobMessage(new Uint8Array(buffer))).toBeUndefined();
  });
});
