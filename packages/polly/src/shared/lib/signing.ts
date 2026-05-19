/**
 * signing — Ed25519 signing and verification for Polly's $meshState
 * primitive (Phase 2). Wraps tweetnacl with a small Polly-flavoured API
 * so the rest of the codebase never imports tweetnacl directly.
 *
 * Every operation that flows through a $meshState transport is signed by
 * the originating peer's private key before transmission and verified by
 * every receiving peer against a known public-key set before being applied.
 * This is the Byzantine-tolerance mechanism: a peer whose private key is
 * compromised can be revoked through a further signed operation, after
 * which honest peers reject anything signed by the revoked key.
 *
 * tweetnacl uses the Ed25519 curve. Public keys and signatures are 32 and
 * 64 bytes respectively, which keeps the per-op overhead small enough that
 * signing every Automerge sync message is feasible even on mobile.
 *
 * The shape of the wrapper:
 *
 *   - {@link generateSigningKeyPair} produces a new Ed25519 keypair. The
 *     private key never leaves the device that generated it; the public
 *     key is gossiped through the access set.
 *
 *   - {@link sign} produces a 64-byte detached signature over a payload.
 *
 *   - {@link verify} checks a payload against a signature and a public
 *     key. Returns boolean rather than throwing so call sites can handle
 *     verification failure as a normal control-flow case.
 *
 *   - {@link signEnvelope} and {@link openEnvelope} package payload + sender
 *     id + signature into a single binary envelope, which is what the mesh
 *     network adapter actually puts on the wire.
 */

import nacl from "tweetnacl";

/** Length in bytes of an Ed25519 public key. */
export const PUBLIC_KEY_BYTES = 32;
/** Length in bytes of an Ed25519 secret (private) key. */
export const SECRET_KEY_BYTES = 64;
/** Length in bytes of an Ed25519 detached signature. */
export const SIGNATURE_BYTES = 64;

/**
 * An Ed25519 keypair. The {@link publicKey} is safe to share with peers;
 * the {@link secretKey} must never leave the device.
 */
export interface SigningKeyPair {
  publicKey: Uint8Array;
  secretKey: Uint8Array;
}

/**
 * A signed envelope. The wire format is the concatenation of the sender id
 * length, the sender id bytes, the signature, and the payload. Callers
 * shouldn't rely on the exact layout — use {@link signEnvelope} and
 * {@link openEnvelope} to round-trip.
 */
export interface SignedEnvelope {
  /** Stable sender peer identifier (UTF-8 string). The receiving side uses
   * this to look up the sender's public key in the document's access set. */
  senderId: string;
  /** The original payload bytes, untouched. */
  payload: Uint8Array;
  /** 64-byte Ed25519 signature over the payload. */
  signature: Uint8Array;
}

/** Errors thrown by the signing subsystem. */
export class SigningError extends Error {
  readonly code:
    | "invalid-secret-key"
    | "invalid-public-key"
    | "invalid-signature-length"
    | "envelope-malformed";

  constructor(message: string, code: SigningError["code"]) {
    super(message);
    this.name = "SigningError";
    this.code = code;
  }
}

/**
 * Generate a fresh Ed25519 keypair. Calls into tweetnacl's CSPRNG.
 */
export function generateSigningKeyPair(): SigningKeyPair {
  const pair = nacl.sign.keyPair();
  return {
    publicKey: pair.publicKey,
    secretKey: pair.secretKey,
  };
}

/**
 * Reconstruct a keypair from an existing 64-byte secret key. Useful for
 * loading keys from persistent storage. Throws if the key is the wrong size.
 */
export function signingKeyPairFromSecret(secretKey: Uint8Array): SigningKeyPair {
  if (secretKey.length !== SECRET_KEY_BYTES) {
    throw new SigningError(
      `Ed25519 secret key must be ${SECRET_KEY_BYTES} bytes, got ${secretKey.length}.`,
      "invalid-secret-key"
    );
  }
  const pair = nacl.sign.keyPair.fromSecretKey(secretKey);
  return {
    publicKey: pair.publicKey,
    secretKey: pair.secretKey,
  };
}

/**
 * Produce a 64-byte detached signature over the given payload using the
 * supplied secret key.
 */
export function sign(payload: Uint8Array, secretKey: Uint8Array): Uint8Array {
  if (secretKey.length !== SECRET_KEY_BYTES) {
    throw new SigningError(
      `Ed25519 secret key must be ${SECRET_KEY_BYTES} bytes, got ${secretKey.length}.`,
      "invalid-secret-key"
    );
  }
  return nacl.sign.detached(payload, secretKey);
}

/**
 * Verify a detached signature against a payload and a public key. Returns
 * true if the signature is valid, false otherwise. Wrong-length keys or
 * signatures throw {@link SigningError} so callers can distinguish a bad
 * signature from a misshapen input.
 */
export function verify(payload: Uint8Array, signature: Uint8Array, publicKey: Uint8Array): boolean {
  if (publicKey.length !== PUBLIC_KEY_BYTES) {
    throw new SigningError(
      `Ed25519 public key must be ${PUBLIC_KEY_BYTES} bytes, got ${publicKey.length}.`,
      "invalid-public-key"
    );
  }
  if (signature.length !== SIGNATURE_BYTES) {
    throw new SigningError(
      `Ed25519 signature must be ${SIGNATURE_BYTES} bytes, got ${signature.length}.`,
      "invalid-signature-length"
    );
  }
  return nacl.sign.detached.verify(payload, signature, publicKey);
}

/**
 * Sign a payload and pack it into a {@link SignedEnvelope} along with the
 * sender id. The mesh network adapter calls this on every outgoing message
 * before handing it to the transport.
 */
export function signEnvelope(
  payload: Uint8Array,
  senderId: string,
  secretKey: Uint8Array
): SignedEnvelope {
  const signature = sign(payload, secretKey);
  return { senderId, payload, signature };
}

/**
 * Verify a {@link SignedEnvelope} against the sender's known public key.
 * Returns the inner payload on success, throws on failure. The mesh
 * network adapter calls this on every incoming message before forwarding
 * the payload to the underlying Automerge sync subsystem.
 */
export function openEnvelope(envelope: SignedEnvelope, publicKey: Uint8Array): Uint8Array {
  const ok = verify(envelope.payload, envelope.signature, publicKey);
  if (!ok) {
    throw new SigningError(
      `Signature verification failed for envelope from ${envelope.senderId}.`,
      "envelope-malformed"
    );
  }
  return envelope.payload;
}

/**
 * Serialise a {@link SignedEnvelope} to a single binary blob suitable for
 * transmission over a network adapter. Wire format:
 *
 *   [4 bytes BE: senderId byte length]
 *   [N bytes:    senderId UTF-8]
 *   [64 bytes:   signature]
 *   [remaining:  payload]
 *
 * Callers should not depend on the exact bytes — they should round-trip
 * through {@link encodeSignedEnvelope} / {@link decodeSignedEnvelope}.
 */
export function encodeSignedEnvelope(envelope: SignedEnvelope): Uint8Array {
  const senderBytes = new TextEncoder().encode(envelope.senderId);
  const total = 4 + senderBytes.length + SIGNATURE_BYTES + envelope.payload.length;
  const out = new Uint8Array(total);
  const view = new DataView(out.buffer);
  view.setUint32(0, senderBytes.length, false);
  out.set(senderBytes, 4);
  out.set(envelope.signature, 4 + senderBytes.length);
  out.set(envelope.payload, 4 + senderBytes.length + SIGNATURE_BYTES);
  return out;
}

/**
 * Deserialise a binary envelope produced by {@link encodeSignedEnvelope}.
 * Throws on malformed input.
 */
export function decodeSignedEnvelope(bytes: Uint8Array): SignedEnvelope {
  if (bytes.length < 4 + SIGNATURE_BYTES) {
    throw new SigningError(
      `Envelope too short: ${bytes.length} bytes, need at least ${4 + SIGNATURE_BYTES}.`,
      "envelope-malformed"
    );
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const senderLen = view.getUint32(0, false);
  if (bytes.length < 4 + senderLen + SIGNATURE_BYTES) {
    throw new SigningError(
      `Envelope truncated: declared sender length ${senderLen}, total ${bytes.length}.`,
      "envelope-malformed"
    );
  }
  const senderId = new TextDecoder().decode(bytes.subarray(4, 4 + senderLen));
  const signature = bytes.slice(4 + senderLen, 4 + senderLen + SIGNATURE_BYTES);
  const payload = bytes.slice(4 + senderLen + SIGNATURE_BYTES);
  return { senderId, payload, signature };
}
