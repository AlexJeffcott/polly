/**
 * pairing — Phase 2 first-cut pairing flow for $meshState.
 *
 * Two devices that want to share a $meshState document must exchange three
 * things before sync can begin: the issuer's Ed25519 signing public key
 * (so the receiver can verify ops authored by the issuer), the symmetric
 * document encryption key (so both sides can encrypt and decrypt the
 * shared document), and the issuer's stable peer id (so the receiver
 * knows which entry in its keyring the public key belongs to). This
 * module packs all three into a {@link PairingToken}, serialises it to a
 * compact binary format suitable for QR codes or copy-paste, and provides
 * the matching parse-and-apply flow on the receiving side.
 *
 * Threat model: pairing tokens are transmitted over an out-of-band channel
 * that the user can authenticate visually — typically a QR code on the
 * issuer's device, scanned by the receiver. Because anyone with the token
 * can decrypt and impersonate, the OOB channel is the only authentication.
 * The token includes a TTL (default 10 minutes) so that a token displayed
 * briefly and then dismissed cannot be replayed by an attacker who later
 * gains access to a screenshot. A production deployment would layer a
 * Short Authentication String (SAS) on top — both devices display a code
 * derived from the shared state, and the user verifies they match — but
 * that is a follow-up.
 *
 * The pairing flow is one-way in the Phase 2 first cut. The issuer
 * generates a token and displays it; the receiver applies it and picks
 * up the issuer's keys. The receiver's own keys reach the issuer through
 * the access set: when the receiver sends its first signed op, the issuer
 * records the receiver's public key alongside its peer id and adds it to
 * the keyring. A bidirectional pairing flow that exchanges both sides'
 * keys in a single QR exchange is straightforward to add later but adds
 * UX surface area that is not needed for the mesh transport to work.
 */

import { KEY_BYTES as ENCRYPTION_KEY_BYTES, generateDocumentKey } from "./encryption";
import type { MeshKeyring } from "./mesh-network-adapter";
import {
  generateSigningKeyPair,
  PUBLIC_KEY_BYTES as SIGNING_PUBLIC_KEY_BYTES,
  type SigningKeyPair,
} from "./signing";

/** Current pairing-token format version. Bumped if the wire format changes. */
export const PAIRING_TOKEN_VERSION = 1;

/** Magic header bytes for sanity-checking parsed tokens. ASCII "PPT1". */
export const PAIRING_TOKEN_MAGIC = new Uint8Array([0x50, 0x50, 0x54, 0x31]);

/** Length of the random nonce embedded in every token. */
export const PAIRING_NONCE_BYTES = 16;

/** Default TTL applied when {@link createPairingToken} is called without an
 * explicit `ttlMs` option. */
export const DEFAULT_PAIRING_TTL_MS = 10 * 60 * 1000; // 10 minutes

/**
 * The contents of a pairing token. Both sides operate on this shape; the
 * binary serialisation is purely for transport.
 */
export interface PairingToken {
  /** Format version. {@link PAIRING_TOKEN_VERSION} at the time of writing. */
  version: number;
  /** Stable peer id of the issuing device. The receiver records this as
   * the lookup key for the issuer's public key in its keyring. */
  issuerPeerId: string;
  /** Issuer's Ed25519 signing public key (32 bytes). */
  issuerPublicKey: Uint8Array;
  /** Shared document encryption key (32 bytes). The receiver stores this
   * under {@link documentKeyId} in its keyring. */
  documentKey: Uint8Array;
  /** Identifier under which the receiver stores the document key. For the
   * Phase 2 first cut this is typically the well-known DEFAULT_MESH_KEY_ID
   * from mesh-network-adapter; per-document keys (one entry per Automerge
   * document) are a follow-up. */
  documentKeyId: string;
  /** Unix timestamp (milliseconds) after which the token is considered
   * expired and {@link applyPairingToken} refuses to use it. */
  expiresAt: number;
  /** 16-byte random nonce. Carried through serialisation so two tokens
   * with otherwise-identical contents are still distinguishable. */
  nonce: Uint8Array;
}

/** Errors thrown by the pairing subsystem. */
export class PairingError extends Error {
  readonly code:
    | "expired"
    | "wrong-magic"
    | "unknown-version"
    | "truncated"
    | "invalid-public-key"
    | "invalid-document-key"
    | "invalid-nonce";

  constructor(message: string, code: PairingError["code"]) {
    super(message);
    this.name = "PairingError";
    this.code = code;
  }
}

/**
 * Options for {@link createPairingToken}. The signing identity and the
 * document key are required; everything else is optional with sensible
 * defaults.
 */
export interface CreatePairingTokenOptions {
  /** The issuing device's signing keypair. Only the public key ends up in
   * the token; the secret never leaves the issuer. */
  identity: SigningKeyPair;
  /** Stable peer id for the issuing device. */
  issuerPeerId: string;
  /** The symmetric document key the receiver should adopt. If omitted, a
   * fresh key is generated and the caller is responsible for using the
   * same key on the issuing side too. */
  documentKey?: Uint8Array;
  /** Identifier under which the receiver stores the document key. */
  documentKeyId: string;
  /** Time-to-live in milliseconds. Defaults to {@link DEFAULT_PAIRING_TTL_MS}. */
  ttlMs?: number;
  /** Override the current time. Intended for tests; production code should
   * not pass this. */
  now?: () => number;
}

/**
 * Generate a fresh {@link PairingToken}. The token is ready to be
 * serialised and displayed to the receiver via an OOB channel.
 */
export function createPairingToken(options: CreatePairingTokenOptions): PairingToken {
  const now = options.now ? options.now() : Date.now();
  const ttlMs = options.ttlMs ?? DEFAULT_PAIRING_TTL_MS;
  const documentKey = options.documentKey ?? generateDocumentKey();
  const nonce = randomBytes(PAIRING_NONCE_BYTES);

  return {
    version: PAIRING_TOKEN_VERSION,
    issuerPeerId: options.issuerPeerId,
    issuerPublicKey: options.identity.publicKey,
    documentKey,
    documentKeyId: options.documentKeyId,
    expiresAt: now + ttlMs,
    nonce,
  };
}

/**
 * Generate a fresh pairing token *and* a fresh signing keypair in one call.
 * Convenience for first-time setup where the device has no existing
 * identity yet. Returns both so the caller can persist the keypair and
 * then display the token.
 */
export function createPairingTokenWithFreshIdentity(args: {
  issuerPeerId: string;
  documentKeyId: string;
  ttlMs?: number;
  now?: () => number;
}): { identity: SigningKeyPair; token: PairingToken } {
  const identity = generateSigningKeyPair();
  const token = createPairingToken({
    identity,
    issuerPeerId: args.issuerPeerId,
    documentKeyId: args.documentKeyId,
    ttlMs: args.ttlMs,
    now: args.now,
  });
  return { identity, token };
}

/**
 * Check whether a token has expired against the current wall-clock time
 * (or an injected `now`).
 */
export function isPairingTokenExpired(token: PairingToken, now?: () => number): boolean {
  const t = now ? now() : Date.now();
  return t >= token.expiresAt;
}

/**
 * Apply a parsed and validated token to a {@link MeshKeyring}. Mutates the
 * keyring in place: adds the issuer's public key to {@link MeshKeyring.knownPeers}
 * and the document key to {@link MeshKeyring.documentKeys}.
 *
 * Throws {@link PairingError} with code "expired" if the token's TTL has
 * elapsed. The receiver is expected to apply the token promptly after
 * scanning; rejecting expired tokens prevents replay of long-lived
 * captures.
 */
export function applyPairingToken(
  token: PairingToken,
  keyring: MeshKeyring,
  options: { now?: () => number } = {}
): void {
  if (isPairingTokenExpired(token, options.now)) {
    throw new PairingError(
      `Pairing token from ${token.issuerPeerId} expired at ${new Date(token.expiresAt).toISOString()}.`,
      "expired"
    );
  }
  keyring.knownPeers.set(token.issuerPeerId, token.issuerPublicKey);
  keyring.documentKeys.set(token.documentKeyId, token.documentKey);
}

// ─── binary serialisation ──────────────────────────────────────────────────

/**
 * Serialise a token to a binary blob. The wire format is:
 *
 *   [4 bytes:  magic "PPT1"]
 *   [1 byte:   version]
 *   [4 bytes BE: issuer id byte length]
 *   [N bytes:  issuer id UTF-8]
 *   [32 bytes: issuer public key]
 *   [32 bytes: document key]
 *   [4 bytes BE: document key id byte length]
 *   [M bytes:  document key id UTF-8]
 *   [8 bytes BE: expiresAt (uint64 milliseconds)]
 *   [16 bytes: nonce]
 *
 * Use {@link encodePairingToken} to round-trip through a base64 string.
 */
export function serialisePairingToken(token: PairingToken): Uint8Array {
  validateForSerialisation(token);
  const issuerBytes = new TextEncoder().encode(token.issuerPeerId);
  const keyIdBytes = new TextEncoder().encode(token.documentKeyId);

  const total =
    PAIRING_TOKEN_MAGIC.length +
    1 + // version
    4 + // issuer id length
    issuerBytes.length +
    SIGNING_PUBLIC_KEY_BYTES +
    ENCRYPTION_KEY_BYTES +
    4 + // doc key id length
    keyIdBytes.length +
    8 + // expiresAt
    PAIRING_NONCE_BYTES;

  const out = new Uint8Array(total);
  let offset = 0;

  out.set(PAIRING_TOKEN_MAGIC, offset);
  offset += PAIRING_TOKEN_MAGIC.length;

  out[offset] = token.version;
  offset += 1;

  const view = new DataView(out.buffer);
  view.setUint32(offset, issuerBytes.length, false);
  offset += 4;
  out.set(issuerBytes, offset);
  offset += issuerBytes.length;

  out.set(token.issuerPublicKey, offset);
  offset += SIGNING_PUBLIC_KEY_BYTES;

  out.set(token.documentKey, offset);
  offset += ENCRYPTION_KEY_BYTES;

  view.setUint32(offset, keyIdBytes.length, false);
  offset += 4;
  out.set(keyIdBytes, offset);
  offset += keyIdBytes.length;

  // Write expiresAt as uint64 BE. JavaScript numbers are float64 but the
  // value is an integer count of milliseconds, well within 53-bit safe
  // range for any practical timestamp.
  view.setBigUint64(offset, BigInt(token.expiresAt), false);
  offset += 8;

  out.set(token.nonce, offset);
  offset += PAIRING_NONCE_BYTES;

  return out;
}

/**
 * Inverse of {@link serialisePairingToken}. Throws {@link PairingError} on
 * malformed input.
 */
export function parsePairingToken(bytes: Uint8Array): PairingToken {
  let offset = 0;

  // Magic
  if (bytes.length < PAIRING_TOKEN_MAGIC.length) {
    throw new PairingError(`Pairing token too short: ${bytes.length} bytes.`, "truncated");
  }
  for (let i = 0; i < PAIRING_TOKEN_MAGIC.length; i++) {
    if (bytes[offset + i] !== PAIRING_TOKEN_MAGIC[i]) {
      throw new PairingError(
        `Pairing token magic mismatch: not a Polly pairing token.`,
        "wrong-magic"
      );
    }
  }
  offset += PAIRING_TOKEN_MAGIC.length;

  // Version
  if (bytes.length < offset + 1) {
    throw new PairingError("Pairing token truncated at version.", "truncated");
  }
  const version = bytes[offset] as unknown as number;
  offset += 1;
  if (version !== PAIRING_TOKEN_VERSION) {
    throw new PairingError(
      `Unknown pairing token version: ${version}. This Polly build supports version ${PAIRING_TOKEN_VERSION}.`,
      "unknown-version"
    );
  }

  // Issuer id
  if (bytes.length < offset + 4) {
    throw new PairingError("Pairing token truncated at issuer id length.", "truncated");
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const issuerLen = view.getUint32(offset, false);
  offset += 4;
  if (bytes.length < offset + issuerLen) {
    throw new PairingError("Pairing token truncated at issuer id.", "truncated");
  }
  const issuerPeerId = new TextDecoder().decode(bytes.subarray(offset, offset + issuerLen));
  offset += issuerLen;

  // Issuer public key
  if (bytes.length < offset + SIGNING_PUBLIC_KEY_BYTES) {
    throw new PairingError("Pairing token truncated at public key.", "truncated");
  }
  const issuerPublicKey = bytes.slice(offset, offset + SIGNING_PUBLIC_KEY_BYTES);
  offset += SIGNING_PUBLIC_KEY_BYTES;

  // Document key
  if (bytes.length < offset + ENCRYPTION_KEY_BYTES) {
    throw new PairingError("Pairing token truncated at document key.", "truncated");
  }
  const documentKey = bytes.slice(offset, offset + ENCRYPTION_KEY_BYTES);
  offset += ENCRYPTION_KEY_BYTES;

  // Document key id
  if (bytes.length < offset + 4) {
    throw new PairingError("Pairing token truncated at document key id length.", "truncated");
  }
  const keyIdLen = view.getUint32(offset, false);
  offset += 4;
  if (bytes.length < offset + keyIdLen) {
    throw new PairingError("Pairing token truncated at document key id.", "truncated");
  }
  const documentKeyId = new TextDecoder().decode(bytes.subarray(offset, offset + keyIdLen));
  offset += keyIdLen;

  // Expires at
  if (bytes.length < offset + 8) {
    throw new PairingError("Pairing token truncated at expiry.", "truncated");
  }
  const expiresAtBig = view.getBigUint64(offset, false);
  offset += 8;
  const expiresAt = Number(expiresAtBig);

  // Nonce
  if (bytes.length < offset + PAIRING_NONCE_BYTES) {
    throw new PairingError("Pairing token truncated at nonce.", "truncated");
  }
  const nonce = bytes.slice(offset, offset + PAIRING_NONCE_BYTES);
  offset += PAIRING_NONCE_BYTES;

  return {
    version,
    issuerPeerId,
    issuerPublicKey,
    documentKey,
    documentKeyId,
    expiresAt,
    nonce,
  };
}

/**
 * Serialise a token and base64-encode it for QR-code or copy-paste display.
 * The encoding uses the standard base64 alphabet (not URL-safe) because
 * QR codes encode bytes directly and do not care about URL safety.
 */
export function encodePairingToken(token: PairingToken): string {
  const bytes = serialisePairingToken(token);
  // btoa expects a binary string. Convert via String.fromCharCode per byte;
  // safe for the ~150-byte token size and avoids the spread-into-fromCharCode
  // pattern that runs into argument-count limits on large arrays.
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary);
}

/**
 * Decode a base64-encoded pairing token produced by {@link encodePairingToken}.
 * Throws {@link PairingError} on malformed input.
 */
export function decodePairingToken(encoded: string): PairingToken {
  let binary: string;
  try {
    binary = atob(encoded);
  } catch {
    throw new PairingError("Pairing token is not valid base64.", "wrong-magic");
  }
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return parsePairingToken(bytes);
}

// ─── helpers ───────────────────────────────────────────────────────────────

function validateForSerialisation(token: PairingToken): void {
  if (token.issuerPublicKey.length !== SIGNING_PUBLIC_KEY_BYTES) {
    throw new PairingError(
      `Issuer public key must be ${SIGNING_PUBLIC_KEY_BYTES} bytes, got ${token.issuerPublicKey.length}.`,
      "invalid-public-key"
    );
  }
  if (token.documentKey.length !== ENCRYPTION_KEY_BYTES) {
    throw new PairingError(
      `Document key must be ${ENCRYPTION_KEY_BYTES} bytes, got ${token.documentKey.length}.`,
      "invalid-document-key"
    );
  }
  if (token.nonce.length !== PAIRING_NONCE_BYTES) {
    throw new PairingError(
      `Nonce must be ${PAIRING_NONCE_BYTES} bytes, got ${token.nonce.length}.`,
      "invalid-nonce"
    );
  }
}

function randomBytes(n: number): Uint8Array {
  const out = new Uint8Array(n);
  crypto.getRandomValues(out);
  return out;
}
