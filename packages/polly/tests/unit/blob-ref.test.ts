import { describe, expect, test } from "bun:test";
import { type BlobRef, computeBlobHash, createBlobRef, isBlobRef } from "@/shared/lib/blob-ref";

describe("computeBlobHash", () => {
  test("produces a 64-character lowercase hex digest", async () => {
    const bytes = new TextEncoder().encode("hello");
    const hash = await computeBlobHash(bytes);
    expect(hash).toMatch(/^[0-9a-f]{64}$/);
  });

  test("matches the known SHA-256 of 'hello'", async () => {
    const bytes = new TextEncoder().encode("hello");
    const hash = await computeBlobHash(bytes);
    const expected = "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824";
    expect(hash).toBe(expected);
  });

  test("matches the known SHA-256 of the empty input", async () => {
    const hash = await computeBlobHash(new Uint8Array(0));
    const expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
    expect(hash).toBe(expected);
  });

  test("is deterministic for identical inputs", async () => {
    const bytes = new TextEncoder().encode("polly");
    const a = await computeBlobHash(bytes);
    const b = await computeBlobHash(bytes);
    expect(a).toBe(b);
  });

  test("produces different hashes for different inputs", async () => {
    const a = await computeBlobHash(new TextEncoder().encode("a"));
    const b = await computeBlobHash(new TextEncoder().encode("b"));
    expect(a).not.toBe(b);
  });
});

describe("createBlobRef", () => {
  test("constructs a BlobRef whose hash matches computeBlobHash", async () => {
    const bytes = new TextEncoder().encode("hello");
    const ref = await createBlobRef({
      bytes,
      filename: "greeting.txt",
      mimeType: "text/plain",
    });
    const expectedHash = await computeBlobHash(bytes);
    expect(ref.hash).toBe(expectedHash);
  });

  test("records the exact size of the input bytes", async () => {
    const bytes = new Uint8Array([1, 2, 3, 4, 5]);
    const ref = await createBlobRef({
      bytes,
      filename: "five.bin",
      mimeType: "application/octet-stream",
    });
    expect(ref.size).toBe(5);
  });

  test("carries filename and mimeType verbatim", async () => {
    const bytes = new Uint8Array([0]);
    const ref = await createBlobRef({
      bytes,
      filename: "weird name with spaces.bin",
      mimeType: "application/x-custom",
    });
    expect(ref.filename).toBe("weird name with spaces.bin");
    expect(ref.mimeType).toBe("application/x-custom");
  });

  test("produces the same hash when filename or mimeType differ", async () => {
    const bytes = new TextEncoder().encode("same bytes");
    const a = await createBlobRef({
      bytes,
      filename: "one.txt",
      mimeType: "text/plain",
    });
    const b = await createBlobRef({
      bytes,
      filename: "two.md",
      mimeType: "text/markdown",
    });
    expect(a.hash).toBe(b.hash);
    expect(a.filename).not.toBe(b.filename);
  });
});

describe("isBlobRef", () => {
  test("accepts a valid BlobRef", () => {
    const ref: BlobRef = {
      hash: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
      size: 0,
      filename: "empty.bin",
      mimeType: "application/octet-stream",
    };
    expect(isBlobRef(ref)).toBe(true);
  });

  test("rejects null", () => {
    expect(isBlobRef(null)).toBe(false);
  });

  test("rejects undefined", () => {
    expect(isBlobRef(undefined)).toBe(false);
  });

  test("rejects a plain string", () => {
    expect(isBlobRef("not a ref")).toBe(false);
  });

  test("rejects an object with missing fields", () => {
    expect(
      isBlobRef({
        hash: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        size: 0,
      })
    ).toBe(false);
  });

  test("rejects a hash that is not 64 lowercase hex characters", () => {
    expect(
      isBlobRef({
        hash: "not-a-hash",
        size: 0,
        filename: "x",
        mimeType: "y",
      })
    ).toBe(false);
  });

  test("rejects a hash with uppercase hex characters", () => {
    expect(
      isBlobRef({
        hash: "E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855",
        size: 0,
        filename: "x",
        mimeType: "y",
      })
    ).toBe(false);
  });

  test("rejects a non-integer size", () => {
    expect(
      isBlobRef({
        hash: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        size: 1.5,
        filename: "x",
        mimeType: "y",
      })
    ).toBe(false);
  });

  test("rejects a negative size", () => {
    expect(
      isBlobRef({
        hash: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        size: -1,
        filename: "x",
        mimeType: "y",
      })
    ).toBe(false);
  });

  test("accepts the output of createBlobRef", async () => {
    const ref = await createBlobRef({
      bytes: new TextEncoder().encode("polly"),
      filename: "name",
      mimeType: "text/plain",
    });
    expect(isBlobRef(ref)).toBe(true);
  });
});
