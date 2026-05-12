/**
 * Unit tests for the sync-fragment wire format.
 *
 * Covers the pure helpers in isolation: chunking, framing, parsing, and
 * reassembly. Adapter-level interception is tested separately against a
 * loopback data channel in mesh-webrtc-adapter-fragment.test.ts.
 */

import { describe, expect, test } from "bun:test";
import {
  chunkSyncMessage,
  isSyncFragmentType,
  parseSyncFragment,
  reassembleSyncFragments,
  SYNC_FRAGMENT_CHUNK_SIZE,
  SYNC_FRAGMENT_THRESHOLD,
  serialiseSyncFragment,
} from "@/shared/lib/sync-fragment";

describe("chunkSyncMessage", () => {
  test("splits a message larger than the chunk size into N ordered fragments", () => {
    const bytes = new Uint8Array(SYNC_FRAGMENT_CHUNK_SIZE * 3 + 17);
    for (let i = 0; i < bytes.length; i++) bytes[i] = i & 0xff;
    const fragments = chunkSyncMessage(bytes, "id-1");
    expect(fragments).toHaveLength(4);
    for (let i = 0; i < fragments.length; i++) {
      const fragment = fragments[i];
      if (!fragment) throw new Error("missing fragment");
      const parsed = parseSyncFragment(fragment);
      if (!parsed) throw new Error("parse failed");
      expect(parsed.header.type).toBe("sync-fragment");
      expect(parsed.header.id).toBe("id-1");
      expect(parsed.header.index).toBe(i);
      expect(parsed.header.total).toBe(4);
    }
  });

  test("produces a single fragment at exactly chunkSize bytes", () => {
    const bytes = new Uint8Array(SYNC_FRAGMENT_CHUNK_SIZE);
    const fragments = chunkSyncMessage(bytes, "id-edge");
    expect(fragments).toHaveLength(1);
    const first = fragments[0];
    if (!first) throw new Error("missing fragment");
    const parsed = parseSyncFragment(first);
    expect(parsed?.header.total).toBe(1);
    expect(parsed?.data.length).toBe(SYNC_FRAGMENT_CHUNK_SIZE);
  });

  test("produces one fragment for an empty payload", () => {
    const fragments = chunkSyncMessage(new Uint8Array(0), "id-empty");
    expect(fragments).toHaveLength(1);
    const first = fragments[0];
    if (!first) throw new Error("missing fragment");
    const parsed = parseSyncFragment(first);
    expect(parsed?.header.total).toBe(1);
    expect(parsed?.data.length).toBe(0);
  });
});

describe("isSyncFragmentType", () => {
  test("matches a frame produced by serialiseSyncFragment", () => {
    const frame = serialiseSyncFragment(
      { type: "sync-fragment", id: "x", index: 0, total: 1 },
      new Uint8Array([1, 2, 3])
    );
    expect(isSyncFragmentType(frame)).toBe(true);
  });

  test("does not match a frame whose header type is something else", () => {
    const fake = new TextEncoder().encode('{"type":"ephemeral"}');
    const buf = new ArrayBuffer(4 + fake.length);
    const view = new DataView(buf);
    view.setUint32(0, fake.length, false);
    new Uint8Array(buf).set(fake, 4);
    expect(isSyncFragmentType(new Uint8Array(buf))).toBe(false);
  });

  test("does not match a blob-prefixed type", () => {
    const blobHeader = new TextEncoder().encode('{"type":"blob-chunk"}');
    const buf = new ArrayBuffer(4 + blobHeader.length);
    const view = new DataView(buf);
    view.setUint32(0, blobHeader.length, false);
    new Uint8Array(buf).set(blobHeader, 4);
    expect(isSyncFragmentType(new Uint8Array(buf))).toBe(false);
  });

  test("returns false on truncated input", () => {
    expect(isSyncFragmentType(new Uint8Array([0, 0, 0]))).toBe(false);
    const buf = new ArrayBuffer(4);
    new DataView(buf).setUint32(0, 999, false);
    expect(isSyncFragmentType(new Uint8Array(buf))).toBe(false);
  });
});

describe("parseSyncFragment", () => {
  test("round-trips header and data", () => {
    const data = new Uint8Array([7, 8, 9, 10]);
    const frame = serialiseSyncFragment(
      { type: "sync-fragment", id: "rt", index: 2, total: 5 },
      data
    );
    const parsed = parseSyncFragment(frame);
    expect(parsed?.header).toEqual({
      type: "sync-fragment",
      id: "rt",
      index: 2,
      total: 5,
    });
    expect(parsed?.data).toEqual(data);
  });

  test("returns undefined for a frame whose header type is not sync-fragment", () => {
    const otherHeader = new TextEncoder().encode('{"type":"other"}');
    const buf = new ArrayBuffer(4 + otherHeader.length + 2);
    const view = new DataView(buf);
    view.setUint32(0, otherHeader.length, false);
    const out = new Uint8Array(buf);
    out.set(otherHeader, 4);
    out.set([1, 2], 4 + otherHeader.length);
    expect(parseSyncFragment(out)).toBeUndefined();
  });

  test("returns undefined for malformed JSON header", () => {
    const bogus = new TextEncoder().encode("{not json");
    const buf = new ArrayBuffer(4 + bogus.length);
    const view = new DataView(buf);
    view.setUint32(0, bogus.length, false);
    new Uint8Array(buf).set(bogus, 4);
    expect(parseSyncFragment(new Uint8Array(buf))).toBeUndefined();
  });
});

describe("reassembleSyncFragments", () => {
  test("rebuilds the original bytes from fragmented input", () => {
    const original = new Uint8Array(SYNC_FRAGMENT_CHUNK_SIZE * 2 + 9);
    for (let i = 0; i < original.length; i++) original[i] = (i * 31) & 0xff;
    const fragments = chunkSyncMessage(original, "rebuild");
    const chunks = new Map<number, Uint8Array>();
    for (const fragment of fragments) {
      const parsed = parseSyncFragment(fragment);
      if (!parsed) throw new Error("parse failed");
      chunks.set(parsed.header.index, parsed.data);
    }
    const reassembled = reassembleSyncFragments(chunks, fragments.length);
    expect(reassembled.length).toBe(original.length);
    expect(reassembled).toEqual(original);
  });

  test("throws when a fragment index is missing", () => {
    const map = new Map<number, Uint8Array>([
      [0, new Uint8Array([1])],
      [2, new Uint8Array([3])],
    ]);
    expect(() => reassembleSyncFragments(map, 3)).toThrow(/missing fragment 1/);
  });
});

describe("constants", () => {
  test("threshold and chunk size sit below the 256 KiB SCTP cap with room for the framing header", () => {
    expect(SYNC_FRAGMENT_THRESHOLD).toBeLessThanOrEqual(256 * 1024);
    expect(SYNC_FRAGMENT_CHUNK_SIZE).toBeLessThanOrEqual(256 * 1024);
  });
});
