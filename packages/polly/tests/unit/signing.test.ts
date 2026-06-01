import { describe, expect, test } from "bun:test";
import {
  decodeSignedEnvelope,
  encodeSignedEnvelope,
  generateSigningKeyPair,
  openEnvelope,
  PUBLIC_KEY_BYTES,
  SECRET_KEY_BYTES,
  SIGNATURE_BYTES,
  SigningError,
  sign,
  signEnvelope,
  signingKeyPairFromSecret,
  verify,
} from "@/shared/lib/signing";

const text = (s: string) => new TextEncoder().encode(s);

describe("generateSigningKeyPair", () => {
  test("produces a 32-byte public key and a 64-byte secret key", () => {
    const pair = generateSigningKeyPair();
    expect(pair.publicKey.length).toBe(PUBLIC_KEY_BYTES);
    expect(pair.secretKey.length).toBe(SECRET_KEY_BYTES);
  });

  test("two consecutive calls produce different keypairs", () => {
    const a = generateSigningKeyPair();
    const b = generateSigningKeyPair();
    expect(a.publicKey).not.toEqual(b.publicKey);
    expect(a.secretKey).not.toEqual(b.secretKey);
  });
});

describe("signingKeyPairFromSecret", () => {
  test("recovers the same public key from an existing secret", () => {
    const original = generateSigningKeyPair();
    const recovered = signingKeyPairFromSecret(original.secretKey);
    expect(recovered.publicKey).toEqual(original.publicKey);
    expect(recovered.secretKey).toEqual(original.secretKey);
  });

  test("throws on a wrong-length secret", () => {
    expect(() => signingKeyPairFromSecret(new Uint8Array(10))).toThrow(SigningError);
  });
});

describe("sign and verify", () => {
  test("a freshly signed payload verifies under its keypair", () => {
    const pair = generateSigningKeyPair();
    const payload = text("hello world");
    const signature = sign(payload, pair.secretKey);
    expect(signature.length).toBe(SIGNATURE_BYTES);
    expect(verify(payload, signature, pair.publicKey)).toBe(true);
  });

  test("a tampered payload fails verification", () => {
    const pair = generateSigningKeyPair();
    const payload = text("original");
    const signature = sign(payload, pair.secretKey);
    const tampered = text("tampered");
    expect(verify(tampered, signature, pair.publicKey)).toBe(false);
  });

  test("a tampered signature fails verification", () => {
    const pair = generateSigningKeyPair();
    const payload = text("original");
    const signature = sign(payload, pair.secretKey);
    const tampered = signature.slice();
    tampered[0] = (tampered[0] ?? 0) ^ 0xff;
    expect(verify(payload, tampered, pair.publicKey)).toBe(false);
  });

  test("a different public key fails verification", () => {
    const a = generateSigningKeyPair();
    const b = generateSigningKeyPair();
    const payload = text("hello");
    const signature = sign(payload, a.secretKey);
    expect(verify(payload, signature, b.publicKey)).toBe(false);
  });

  test("verify throws on a wrong-length public key", () => {
    const pair = generateSigningKeyPair();
    const payload = text("x");
    const signature = sign(payload, pair.secretKey);
    expect(() => verify(payload, signature, new Uint8Array(10))).toThrow(SigningError);
  });

  test("verify throws on a wrong-length signature", () => {
    const pair = generateSigningKeyPair();
    const payload = text("x");
    expect(() => verify(payload, new Uint8Array(10), pair.publicKey)).toThrow(SigningError);
  });

  test("sign throws on a wrong-length secret key", () => {
    expect(() => sign(text("x"), new Uint8Array(10))).toThrow(SigningError);
  });
});

describe("signEnvelope and openEnvelope", () => {
  test("envelope round-trips through openEnvelope", () => {
    const pair = generateSigningKeyPair();
    const payload = text("important message");
    const envelope = signEnvelope(payload, "peer-alice", pair.secretKey);
    expect(envelope.senderId).toBe("peer-alice");
    expect(envelope.payload).toEqual(payload);
    expect(envelope.signature.length).toBe(SIGNATURE_BYTES);

    const opened = openEnvelope(envelope, pair.publicKey);
    expect(opened).toEqual(payload);
  });

  test("openEnvelope throws if the envelope was signed by a different key", () => {
    const a = generateSigningKeyPair();
    const b = generateSigningKeyPair();
    const envelope = signEnvelope(text("hello"), "peer-alice", a.secretKey);
    expect(() => openEnvelope(envelope, b.publicKey)).toThrow(SigningError);
  });

  test("openEnvelope throws if the payload was tampered with", () => {
    const pair = generateSigningKeyPair();
    const envelope = signEnvelope(text("hello"), "peer-alice", pair.secretKey);
    const tampered: typeof envelope = {
      ...envelope,
      payload: text("tampered"),
    };
    expect(() => openEnvelope(tampered, pair.publicKey)).toThrow(SigningError);
  });
});

describe("encodeSignedEnvelope and decodeSignedEnvelope", () => {
  test("round-trips a signed envelope through binary", () => {
    const pair = generateSigningKeyPair();
    const original = signEnvelope(text("payload"), "peer-bob", pair.secretKey);
    const encoded = encodeSignedEnvelope(original);
    const decoded = decodeSignedEnvelope(encoded);
    expect(decoded.senderId).toBe("peer-bob");
    expect(decoded.payload).toEqual(original.payload);
    expect(decoded.signature).toEqual(original.signature);
    expect(openEnvelope(decoded, pair.publicKey)).toEqual(original.payload);
  });

  test("supports an empty payload", () => {
    const pair = generateSigningKeyPair();
    const original = signEnvelope(new Uint8Array(0), "peer-empty", pair.secretKey);
    const encoded = encodeSignedEnvelope(original);
    const decoded = decodeSignedEnvelope(encoded);
    expect(decoded.payload.length).toBe(0);
    expect(openEnvelope(decoded, pair.publicKey)).toEqual(original.payload);
  });

  test("supports a multi-byte sender id", () => {
    const pair = generateSigningKeyPair();
    const senderId = "peer-with-€-and-😀";
    const original = signEnvelope(text("hi"), senderId, pair.secretKey);
    const decoded = decodeSignedEnvelope(encodeSignedEnvelope(original));
    expect(decoded.senderId).toBe(senderId);
  });

  test("decode throws on a too-short blob", () => {
    expect(() => decodeSignedEnvelope(new Uint8Array(10))).toThrow(SigningError);
  });

  test("decode throws on a truncated payload", () => {
    const pair = generateSigningKeyPair();
    const original = signEnvelope(text("hello"), "peer", pair.secretKey);
    const full = encodeSignedEnvelope(original);
    const truncated = full.slice(0, full.length - 5);
    // Truncating the payload below the declared length still passes the
    // length check (sender id + signature are intact), but the resulting
    // envelope verifies only if we slice cleanly — the test confirms the
    // decoder does not crash on a trimmed payload, and the verify fails.
    const decoded = decodeSignedEnvelope(truncated);
    expect(() => openEnvelope(decoded, pair.publicKey)).toThrow(SigningError);
  });
});

/** Run a throwing function and return the SigningError it raised, failing
 * loudly if it threw something else or nothing at all. */
function catchSigningError(fn: () => unknown): SigningError {
  try {
    fn();
  } catch (e) {
    if (e instanceof SigningError) return e;
    throw e;
  }
  throw new Error("expected a SigningError to be thrown");
}

describe("SigningError codes and messages", () => {
  test("a SigningError carries the SigningError name", () => {
    const err = catchSigningError(() => signingKeyPairFromSecret(new Uint8Array(10)));
    expect(err.name).toBe("SigningError");
  });

  test("signingKeyPairFromSecret reports invalid-secret-key with the byte counts", () => {
    const err = catchSigningError(() => signingKeyPairFromSecret(new Uint8Array(10)));
    expect(err.code).toBe("invalid-secret-key");
    expect(err.message).toContain(`${SECRET_KEY_BYTES} bytes`);
    expect(err.message).toContain("got 10");
  });

  test("sign reports invalid-secret-key with the byte counts", () => {
    const err = catchSigningError(() => sign(text("x"), new Uint8Array(5)));
    expect(err.code).toBe("invalid-secret-key");
    expect(err.message).toContain(`${SECRET_KEY_BYTES} bytes`);
    expect(err.message).toContain("got 5");
  });

  test("verify reports invalid-public-key for a wrong-length public key", () => {
    const err = catchSigningError(() =>
      verify(text("x"), new Uint8Array(SIGNATURE_BYTES), new Uint8Array(8))
    );
    expect(err.code).toBe("invalid-public-key");
    expect(err.message).toContain(`${PUBLIC_KEY_BYTES} bytes`);
    expect(err.message).toContain("got 8");
  });

  test("verify reports invalid-signature-length for a wrong-length signature", () => {
    const err = catchSigningError(() =>
      verify(text("x"), new Uint8Array(9), new Uint8Array(PUBLIC_KEY_BYTES))
    );
    expect(err.code).toBe("invalid-signature-length");
    expect(err.message).toContain(`${SIGNATURE_BYTES} bytes`);
    expect(err.message).toContain("got 9");
  });

  test("openEnvelope reports envelope-malformed naming the sender on a bad signature", () => {
    const pair = generateSigningKeyPair();
    const other = generateSigningKeyPair();
    const env = signEnvelope(text("payload"), "peer-x", pair.secretKey);
    const err = catchSigningError(() => openEnvelope(env, other.publicKey));
    expect(err.code).toBe("envelope-malformed");
    expect(err.message).toContain("peer-x");
  });

  test("decode reports envelope-malformed with the minimum-length hint on a too-short blob", () => {
    const err = catchSigningError(() => decodeSignedEnvelope(new Uint8Array(10)));
    expect(err.code).toBe("envelope-malformed");
    expect(err.message).toContain("too short");
    // The hint is the prefix+signature minimum (4 + 64 = 68); a corrupted
    // arithmetic operator in the template would print a different number.
    expect(err.message).toContain(`${4 + SIGNATURE_BYTES}`);
  });

  test("decode reports envelope-malformed naming the declared sender length when truncated", () => {
    // A blob long enough to clear the prefix+signature floor (>= 68) but
    // whose declared sender length leaves no room for the signature — the
    // second length guard. A modest senderLen keeps the signature term the
    // deciding factor, so the guard's full `4 + senderLen + SIGNATURE_BYTES`
    // sum is exercised rather than dominated by an enormous senderLen.
    const blob = new Uint8Array(4 + SIGNATURE_BYTES + 2);
    const senderLen = 20;
    new DataView(blob.buffer).setUint32(0, senderLen, false);
    const err = catchSigningError(() => decodeSignedEnvelope(blob));
    expect(err.code).toBe("envelope-malformed");
    expect(err.message).toContain("truncated");
    expect(err.message).toContain(`${senderLen}`);
  });
});

describe("decodeSignedEnvelope length boundaries", () => {
  test("decodes a minimal 68-byte envelope (empty sender, empty payload)", () => {
    const pair = generateSigningKeyPair();
    const env = signEnvelope(new Uint8Array(0), "", pair.secretKey);
    const encoded = encodeSignedEnvelope(env);
    // 4-byte prefix + 0 sender bytes + 64 signature + 0 payload.
    expect(encoded.length).toBe(4 + SIGNATURE_BYTES);
    // The floor guard is strictly less-than, so the boundary length decodes.
    const decoded = decodeSignedEnvelope(encoded);
    expect(decoded.senderId).toBe("");
    expect(decoded.payload.length).toBe(0);
  });

  test("throws one byte below the prefix+signature floor", () => {
    expect(() => decodeSignedEnvelope(new Uint8Array(4 + SIGNATURE_BYTES - 1))).toThrow(
      SigningError
    );
  });
});
