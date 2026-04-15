import { describe, expect, test } from "bun:test";
import { generateDocumentKey } from "@/shared/lib/encryption";
import { DEFAULT_MESH_KEY_ID, type MeshKeyring } from "@/shared/lib/mesh-network-adapter";
import {
  applyPairingToken,
  createPairingToken,
  createPairingTokenWithFreshIdentity,
  DEFAULT_PAIRING_TTL_MS,
  decodePairingToken,
  encodePairingToken,
  isPairingTokenExpired,
  PAIRING_NONCE_BYTES,
  PAIRING_TOKEN_VERSION,
  PairingError,
  parsePairingToken,
  serialisePairingToken,
} from "@/shared/lib/pairing";
import {
  generateSigningKeyPair,
  PUBLIC_KEY_BYTES as SIGNING_PUBLIC_KEY_BYTES,
} from "@/shared/lib/signing";

function makeKeyring(): MeshKeyring {
  return {
    identity: generateSigningKeyPair(),
    knownPeers: new Map(),
    documentKeys: new Map(),
    revokedPeers: new Set(),
  };
}

describe("createPairingToken", () => {
  test("populates every field with sensible defaults", () => {
    const identity = generateSigningKeyPair();
    const before = Date.now();
    const token = createPairingToken({
      identity,
      issuerPeerId: "peer-alice",
      documentKeyId: DEFAULT_MESH_KEY_ID,
    });
    const after = Date.now();

    expect(token.version).toBe(PAIRING_TOKEN_VERSION);
    expect(token.issuerPeerId).toBe("peer-alice");
    expect(token.issuerPublicKey).toEqual(identity.publicKey);
    expect(token.documentKey.length).toBe(32);
    expect(token.documentKeyId).toBe(DEFAULT_MESH_KEY_ID);
    expect(token.nonce.length).toBe(PAIRING_NONCE_BYTES);
    expect(token.expiresAt).toBeGreaterThanOrEqual(before + DEFAULT_PAIRING_TTL_MS);
    expect(token.expiresAt).toBeLessThanOrEqual(after + DEFAULT_PAIRING_TTL_MS);
  });

  test("respects an explicit ttlMs", () => {
    const identity = generateSigningKeyPair();
    const start = 1_700_000_000_000;
    const token = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
      ttlMs: 60_000,
      now: () => start,
    });
    expect(token.expiresAt).toBe(start + 60_000);
  });

  test("uses a caller-supplied document key when provided", () => {
    const identity = generateSigningKeyPair();
    const docKey = generateDocumentKey();
    const token = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKey: docKey,
      documentKeyId: "k",
    });
    expect(token.documentKey).toEqual(docKey);
  });

  test("two consecutive tokens have different nonces", () => {
    const identity = generateSigningKeyPair();
    const a = createPairingToken({ identity, issuerPeerId: "p", documentKeyId: "k" });
    const b = createPairingToken({ identity, issuerPeerId: "p", documentKeyId: "k" });
    expect(a.nonce).not.toEqual(b.nonce);
  });
});

describe("createPairingTokenWithFreshIdentity", () => {
  test("returns both a fresh identity and a matching token", () => {
    const { identity, token } = createPairingTokenWithFreshIdentity({
      issuerPeerId: "peer-fresh",
      documentKeyId: "doc",
    });
    expect(identity.publicKey.length).toBe(SIGNING_PUBLIC_KEY_BYTES);
    expect(token.issuerPublicKey).toEqual(identity.publicKey);
  });
});

describe("isPairingTokenExpired", () => {
  test("returns false for a token whose ttl has not elapsed", () => {
    const identity = generateSigningKeyPair();
    const token = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
      ttlMs: 60_000,
      now: () => 1_000_000,
    });
    expect(isPairingTokenExpired(token, () => 1_010_000)).toBe(false);
  });

  test("returns true once the ttl has elapsed", () => {
    const identity = generateSigningKeyPair();
    const token = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
      ttlMs: 60_000,
      now: () => 1_000_000,
    });
    expect(isPairingTokenExpired(token, () => 1_999_000)).toBe(true);
  });
});

describe("applyPairingToken", () => {
  test("adds the issuer's public key and document key to the keyring", () => {
    const identity = generateSigningKeyPair();
    const docKey = generateDocumentKey();
    const token = createPairingToken({
      identity,
      issuerPeerId: "peer-alice",
      documentKey: docKey,
      documentKeyId: DEFAULT_MESH_KEY_ID,
    });
    const keyring = makeKeyring();
    applyPairingToken(token, keyring);
    expect(keyring.knownPeers.get("peer-alice")).toEqual(identity.publicKey);
    expect(keyring.documentKeys.get(DEFAULT_MESH_KEY_ID)).toEqual(docKey);
  });

  test("throws PairingError with code expired when the token has expired", () => {
    const identity = generateSigningKeyPair();
    const token = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
      ttlMs: 1_000,
      now: () => 1_000_000,
    });
    const keyring = makeKeyring();
    let caught: unknown;
    try {
      applyPairingToken(token, keyring, { now: () => 1_500_000 });
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(PairingError);
    expect((caught as PairingError).code).toBe("expired");
    // Keyring is unchanged on failure.
    expect(keyring.knownPeers.size).toBe(0);
    expect(keyring.documentKeys.size).toBe(0);
  });

  test("does not overwrite unrelated existing entries", () => {
    const aliceIdentity = generateSigningKeyPair();
    const bobIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const keyring = makeKeyring();
    keyring.knownPeers.set("peer-bob", bobIdentity.publicKey);
    keyring.documentKeys.set("other-doc", generateDocumentKey());

    const token = createPairingToken({
      identity: aliceIdentity,
      issuerPeerId: "peer-alice",
      documentKey: docKey,
      documentKeyId: DEFAULT_MESH_KEY_ID,
    });
    applyPairingToken(token, keyring);

    expect(keyring.knownPeers.get("peer-bob")).toEqual(bobIdentity.publicKey);
    expect(keyring.knownPeers.get("peer-alice")).toEqual(aliceIdentity.publicKey);
    expect(keyring.documentKeys.size).toBe(2);
  });
});

describe("serialisePairingToken and parsePairingToken", () => {
  test("round-trips a token through binary", () => {
    const identity = generateSigningKeyPair();
    const original = createPairingToken({
      identity,
      issuerPeerId: "peer-roundtrip",
      documentKeyId: "doc-1",
      ttlMs: 60_000,
      now: () => 1_700_000_000_000,
    });
    const bytes = serialisePairingToken(original);
    const parsed = parsePairingToken(bytes);
    expect(parsed.version).toBe(original.version);
    expect(parsed.issuerPeerId).toBe(original.issuerPeerId);
    expect(parsed.issuerPublicKey).toEqual(original.issuerPublicKey);
    expect(parsed.documentKey).toEqual(original.documentKey);
    expect(parsed.documentKeyId).toBe(original.documentKeyId);
    expect(parsed.expiresAt).toBe(original.expiresAt);
    expect(parsed.nonce).toEqual(original.nonce);
  });

  test("supports a multi-byte issuer id and document key id", () => {
    const identity = generateSigningKeyPair();
    const original = createPairingToken({
      identity,
      issuerPeerId: "peer-with-€-and-😀",
      documentKeyId: "doc-😀",
    });
    const parsed = parsePairingToken(serialisePairingToken(original));
    expect(parsed.issuerPeerId).toBe("peer-with-€-and-😀");
    expect(parsed.documentKeyId).toBe("doc-😀");
  });

  test("parse throws on a wrong magic header", () => {
    const wrongMagic = new Uint8Array([0xff, 0xff, 0xff, 0xff, 0x01]);
    let caught: unknown;
    try {
      parsePairingToken(wrongMagic);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(PairingError);
    expect((caught as PairingError).code).toBe("wrong-magic");
  });

  test("parse throws on an unknown version", () => {
    const identity = generateSigningKeyPair();
    const original = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
    });
    const bytes = serialisePairingToken(original);
    // The version byte is at offset 4 (after the 4-byte magic).
    bytes[4] = 99;
    let caught: unknown;
    try {
      parsePairingToken(bytes);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(PairingError);
    expect((caught as PairingError).code).toBe("unknown-version");
  });

  test("parse throws on a truncated blob", () => {
    const identity = generateSigningKeyPair();
    const original = createPairingToken({
      identity,
      issuerPeerId: "p",
      documentKeyId: "k",
    });
    const bytes = serialisePairingToken(original);
    const truncated = bytes.slice(0, bytes.length - 10);
    let caught: unknown;
    try {
      parsePairingToken(truncated);
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(PairingError);
    expect((caught as PairingError).code).toBe("truncated");
  });
});

describe("encodePairingToken and decodePairingToken", () => {
  test("round-trips a token through base64", () => {
    const identity = generateSigningKeyPair();
    const original = createPairingToken({
      identity,
      issuerPeerId: "peer-base64",
      documentKeyId: "doc-base64",
    });
    const encoded = encodePairingToken(original);
    expect(typeof encoded).toBe("string");
    expect(encoded.length).toBeGreaterThan(0);
    const decoded = decodePairingToken(encoded);
    expect(decoded.issuerPeerId).toBe(original.issuerPeerId);
    expect(decoded.issuerPublicKey).toEqual(original.issuerPublicKey);
    expect(decoded.documentKey).toEqual(original.documentKey);
    expect(decoded.documentKeyId).toBe(original.documentKeyId);
  });

  test("decode throws on an invalid base64 string", () => {
    let caught: unknown;
    try {
      decodePairingToken("not valid base64 ###");
    } catch (err) {
      caught = err;
    }
    expect(caught).toBeInstanceOf(PairingError);
  });
});

describe("end-to-end pairing scenario", () => {
  test("issuer creates a token, encodes it, receiver decodes and applies it", () => {
    // Issuer device sets up.
    const { identity: issuerIdentity, token } = createPairingTokenWithFreshIdentity({
      issuerPeerId: "issuer",
      documentKeyId: DEFAULT_MESH_KEY_ID,
    });

    // The issuer encodes the token for display (e.g. as a QR code).
    const wireString = encodePairingToken(token);

    // Receiver device scans the QR code and gets the wire string.
    // The receiver has its own identity already.
    const receiverIdentity = generateSigningKeyPair();
    const receiverKeyring: MeshKeyring = {
      identity: receiverIdentity,
      knownPeers: new Map(),
      documentKeys: new Map(),
      revokedPeers: new Set(),
    };

    const decoded = decodePairingToken(wireString);
    applyPairingToken(decoded, receiverKeyring);

    // The receiver now has the issuer's public key and the document key.
    expect(receiverKeyring.knownPeers.get("issuer")).toEqual(issuerIdentity.publicKey);
    expect(receiverKeyring.documentKeys.get(DEFAULT_MESH_KEY_ID)).toEqual(token.documentKey);

    // The receiver's own identity is unaffected.
    expect(receiverKeyring.identity).toEqual(receiverIdentity);
  });
});
