import { describe, expect, test } from "bun:test";
import {
  decodeEncryptedEnvelope,
  decrypt,
  decryptOrThrow,
  EncryptionError,
  encodeEncryptedEnvelope,
  encrypt,
  generateDocumentKey,
  KEY_BYTES,
  NONCE_BYTES,
  openEnvelope,
  sealEnvelope,
  TAG_BYTES,
} from "@/shared/lib/encryption";

const text = (s: string) => new TextEncoder().encode(s);

describe("generateDocumentKey", () => {
  test("returns a 32-byte symmetric key", () => {
    const key = generateDocumentKey();
    expect(key.length).toBe(KEY_BYTES);
  });

  test("two consecutive calls return different keys", () => {
    expect(generateDocumentKey()).not.toEqual(generateDocumentKey());
  });
});

describe("encrypt and decrypt", () => {
  test("a freshly encrypted payload round-trips with the same key", () => {
    const key = generateDocumentKey();
    const payload = text("hello world");
    const sealed = encrypt(payload, key);
    expect(sealed.length).toBeGreaterThanOrEqual(NONCE_BYTES + TAG_BYTES);
    const opened = decrypt(sealed, key);
    expect(opened).toEqual(payload);
  });

  test("decrypt returns undefined when the key is wrong", () => {
    const a = generateDocumentKey();
    const b = generateDocumentKey();
    const sealed = encrypt(text("secret"), a);
    expect(decrypt(sealed, b)).toBeUndefined();
  });

  test("decrypt returns undefined when the ciphertext is tampered with", () => {
    const key = generateDocumentKey();
    const sealed = encrypt(text("secret"), key);
    const idx = NONCE_BYTES + 2;
    sealed[idx] = (sealed[idx] ?? 0) ^ 0xff;
    expect(decrypt(sealed, key)).toBeUndefined();
  });

  test("decrypt returns undefined for a too-short blob", () => {
    const key = generateDocumentKey();
    expect(decrypt(new Uint8Array(10), key)).toBeUndefined();
  });

  test("encrypt produces a different sealed blob each time (fresh nonce)", () => {
    const key = generateDocumentKey();
    const payload = text("identical payload");
    const a = encrypt(payload, key);
    const b = encrypt(payload, key);
    expect(a).not.toEqual(b);
    // But both round-trip to the same payload.
    expect(decrypt(a, key)).toEqual(payload);
    expect(decrypt(b, key)).toEqual(payload);
  });

  test("encrypt throws on a wrong-length key", () => {
    expect(() => encrypt(text("x"), new Uint8Array(10))).toThrow(EncryptionError);
  });

  test("decrypt throws on a wrong-length key", () => {
    const key = generateDocumentKey();
    const sealed = encrypt(text("x"), key);
    expect(() => decrypt(sealed, new Uint8Array(10))).toThrow(EncryptionError);
  });
});

describe("decryptOrThrow", () => {
  test("returns the payload on success", () => {
    const key = generateDocumentKey();
    const payload = text("hello");
    const sealed = encrypt(payload, key);
    expect(decryptOrThrow(sealed, key)).toEqual(payload);
  });

  test("throws EncryptionError on a wrong key", () => {
    const a = generateDocumentKey();
    const b = generateDocumentKey();
    const sealed = encrypt(text("x"), a);
    expect(() => decryptOrThrow(sealed, b)).toThrow(EncryptionError);
  });
});

describe("sealEnvelope and openEnvelope", () => {
  test("round-trips a payload through the structured envelope", () => {
    const key = generateDocumentKey();
    const envelope = sealEnvelope(text("important"), "doc-1", key);
    expect(envelope.documentId).toBe("doc-1");
    expect(envelope.sealed.length).toBeGreaterThan(NONCE_BYTES + TAG_BYTES);
    expect(openEnvelope(envelope, key)).toEqual(text("important"));
  });

  test("openEnvelope throws on a wrong key", () => {
    const a = generateDocumentKey();
    const b = generateDocumentKey();
    const envelope = sealEnvelope(text("hello"), "doc-1", a);
    expect(() => openEnvelope(envelope, b)).toThrow(EncryptionError);
  });
});

describe("encodeEncryptedEnvelope and decodeEncryptedEnvelope", () => {
  test("round-trips a structured envelope through binary", () => {
    const key = generateDocumentKey();
    const original = sealEnvelope(text("payload"), "doc-abc", key);
    const encoded = encodeEncryptedEnvelope(original);
    const decoded = decodeEncryptedEnvelope(encoded);
    expect(decoded.documentId).toBe("doc-abc");
    expect(decoded.sealed).toEqual(original.sealed);
    expect(openEnvelope(decoded, key)).toEqual(text("payload"));
  });

  test("supports an empty payload", () => {
    const key = generateDocumentKey();
    const original = sealEnvelope(new Uint8Array(0), "doc-empty", key);
    const decoded = decodeEncryptedEnvelope(encodeEncryptedEnvelope(original));
    expect(openEnvelope(decoded, key)).toEqual(new Uint8Array(0));
  });

  test("supports a multi-byte document id", () => {
    const key = generateDocumentKey();
    const id = "doc-with-€-and-😀";
    const original = sealEnvelope(text("x"), id, key);
    const decoded = decodeEncryptedEnvelope(encodeEncryptedEnvelope(original));
    expect(decoded.documentId).toBe(id);
  });

  test("decode throws on a too-short blob", () => {
    expect(() => decodeEncryptedEnvelope(new Uint8Array(2))).toThrow(EncryptionError);
  });
});

/** Run a throwing function and return the EncryptionError it raised, failing
 * loudly if it threw something else or nothing at all. */
function catchEncryptionError(fn: () => unknown): EncryptionError {
  try {
    fn();
  } catch (e) {
    if (e instanceof EncryptionError) return e;
    throw e;
  }
  throw new Error("expected an EncryptionError to be thrown");
}

describe("EncryptionError codes and messages", () => {
  test("an EncryptionError carries the EncryptionError name", () => {
    const err = catchEncryptionError(() => encrypt(new Uint8Array(1), new Uint8Array(8)));
    expect(err.name).toBe("EncryptionError");
  });

  test("encrypt reports invalid-key-length with the byte counts", () => {
    const err = catchEncryptionError(() => encrypt(new Uint8Array(1), new Uint8Array(8)));
    expect(err.code).toBe("invalid-key-length");
    expect(err.message).toContain(`${KEY_BYTES} bytes`);
    expect(err.message).toContain("got 8");
  });

  test("decrypt reports invalid-key-length with the byte counts", () => {
    const err = catchEncryptionError(() => decrypt(new Uint8Array(40), new Uint8Array(5)));
    expect(err.code).toBe("invalid-key-length");
    expect(err.message).toContain(`${KEY_BYTES} bytes`);
    expect(err.message).toContain("got 5");
  });

  test("decryptOrThrow reports decrypt-failed on a wrong key", () => {
    const key = generateDocumentKey();
    const wrong = generateDocumentKey();
    const sealed = encrypt(new TextEncoder().encode("secret"), key);
    const err = catchEncryptionError(() => decryptOrThrow(sealed, wrong));
    expect(err.code).toBe("decrypt-failed");
    expect(err.message).toContain("Failed to decrypt");
  });

  test("decode reports envelope-malformed with the byte count on a too-short blob", () => {
    const err = catchEncryptionError(() => decodeEncryptedEnvelope(new Uint8Array(2)));
    expect(err.code).toBe("envelope-malformed");
    expect(err.message).toContain("too short");
    expect(err.message).toContain("2 bytes");
  });

  test("decode reports envelope-malformed naming the declared id length when truncated", () => {
    // Length >= 4 (clears the prefix floor) but the declared id length
    // overruns the buffer — the second length guard.
    const blob = new Uint8Array(8);
    new DataView(blob.buffer).setUint32(0, 1000, false);
    const err = catchEncryptionError(() => decodeEncryptedEnvelope(blob));
    expect(err.code).toBe("envelope-malformed");
    expect(err.message).toContain("truncated");
    expect(err.message).toContain("1000");
  });
});

describe("decrypt length floor", () => {
  test("round-trips an empty payload whose sealed blob sits exactly at the nonce+tag floor", () => {
    const key = generateDocumentKey();
    const sealed = encrypt(new Uint8Array(0), key);
    // nonce (24) + tag (16) + zero-length ciphertext = exactly 40 bytes.
    expect(sealed.length).toBe(NONCE_BYTES + TAG_BYTES);
    // The length guard is strictly less-than, so a blob exactly at the floor
    // is decrypted rather than rejected outright.
    const opened = decrypt(sealed, key);
    expect(opened).toBeDefined();
    expect(opened?.length).toBe(0);
  });

  test("returns undefined one byte below the nonce+tag floor", () => {
    const key = generateDocumentKey();
    expect(decrypt(new Uint8Array(NONCE_BYTES + TAG_BYTES - 1), key)).toBeUndefined();
  });
});

describe("decodeEncryptedEnvelope length boundaries", () => {
  test("decodes a bare 4-byte blob (zero-length id, empty sealed)", () => {
    // idLen 0 in exactly the 4-byte prefix: the floor guard is strictly
    // less-than, so this minimal frame decodes rather than being rejected.
    const decoded = decodeEncryptedEnvelope(new Uint8Array(4));
    expect(decoded.documentId).toBe("");
    expect(decoded.sealed.length).toBe(0);
  });

  test("decodes when the total length exactly equals the declared id span", () => {
    // length 8, idLen 4 → 8 === 4 + idLen, so the second guard's strict
    // less-than lets it through with an empty sealed blob.
    const blob = new Uint8Array(8);
    new DataView(blob.buffer).setUint32(0, 4, false);
    const decoded = decodeEncryptedEnvelope(blob);
    expect(decoded.sealed.length).toBe(0);
  });
});
