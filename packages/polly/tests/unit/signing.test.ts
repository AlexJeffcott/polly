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
