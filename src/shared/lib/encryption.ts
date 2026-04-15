/**
 * encryption — symmetric authenticated encryption for Polly's $meshState
 * primitive (Phase 2). Wraps tweetnacl's secretbox (XSalsa20-Poly1305) with
 * a small Polly-flavoured API so the rest of the codebase never imports
 * tweetnacl directly.
 *
 * Every $meshState document has a per-document symmetric key that is
 * provisioned to authorised peers at pairing time and never held by any
 * server. Outgoing operations are encrypted under this key before they
 * touch the network adapter; incoming operations are decrypted on receipt.
 * The signing layer in {@link signing.ts} provides authenticity (proof of
 * who sent the message); this layer provides confidentiality (the bytes
 * are unreadable to anything that does not hold the document key).
 *
 * tweetnacl's secretbox uses a 32-byte symmetric key and a 24-byte nonce.
 * The output of `nacl.secretbox` is the ciphertext concatenated with a
 * 16-byte Poly1305 authentication tag. We package the nonce + ciphertext
 * into a single binary blob using a small length-prefixed envelope so the
 * receiver can recover the nonce without out-of-band coordination.
 *
 *   - {@link generateDocumentKey} returns a fresh 32-byte symmetric key.
 *
 *   - {@link encrypt} produces a sealed blob from a payload and a key.
 *
 *   - {@link decrypt} recovers the payload from a sealed blob and a key.
 *     Returns undefined if the blob is malformed or the authentication
 *     tag does not match (i.e. wrong key or tampered ciphertext) — the
 *     undefined signal lets call sites distinguish "wrong key" from
 *     "structurally invalid" without throwing.
 *
 *   - {@link sealEnvelope} and {@link openEnvelope} are convenience helpers
 *     that wrap encrypt/decrypt in a structured EncryptedEnvelope shape so
 *     the mesh transport layer can handle the binary plumbing uniformly.
 */

import nacl from "tweetnacl";

/** Length in bytes of a secretbox symmetric key. */
export const KEY_BYTES = 32;
/** Length in bytes of a secretbox nonce. */
export const NONCE_BYTES = 24;
/** Length in bytes of the Poly1305 authentication tag. */
export const TAG_BYTES = 16;

/**
 * A sealed blob suitable for storage or network transmission. The wire
 * layout is the concatenation of the nonce and the ciphertext+tag from
 * tweetnacl. Callers should not depend on the exact bytes — round-trip
 * through {@link encrypt} / {@link decrypt} or the envelope helpers.
 */
export type SealedBytes = Uint8Array;

/** Errors thrown by the encryption subsystem. */
export class EncryptionError extends Error {
  readonly code: "invalid-key-length" | "decrypt-failed" | "envelope-malformed";
  constructor(message: string, code: EncryptionError["code"]) {
    super(message);
    this.name = "EncryptionError";
    this.code = code;
  }
}

/**
 * Generate a fresh 32-byte symmetric document key. Calls into tweetnacl's
 * CSPRNG.
 */
export function generateDocumentKey(): Uint8Array {
  return nacl.randomBytes(KEY_BYTES);
}

/**
 * Encrypt a payload under a symmetric key. The returned blob includes a
 * fresh nonce so the receiver does not need any out-of-band coordination
 * to decrypt.
 */
export function encrypt(payload: Uint8Array, key: Uint8Array): SealedBytes {
  if (key.length !== KEY_BYTES) {
    throw new EncryptionError(
      `secretbox key must be ${KEY_BYTES} bytes, got ${key.length}.`,
      "invalid-key-length"
    );
  }
  const nonce = nacl.randomBytes(NONCE_BYTES);
  const ciphertext = nacl.secretbox(payload, nonce, key);
  const out = new Uint8Array(NONCE_BYTES + ciphertext.length);
  out.set(nonce, 0);
  out.set(ciphertext, NONCE_BYTES);
  return out;
}

/**
 * Decrypt a sealed blob under a symmetric key. Returns the original
 * payload on success. Returns undefined if the blob is too short to
 * contain a nonce and tag, or if the authentication tag does not match
 * (which indicates either a wrong key or a tampered ciphertext).
 *
 * The undefined return is deliberate: call sites typically want to fall
 * back to a different key or surface a "could not decrypt" message rather
 * than catching an exception. Use {@link decryptOrThrow} when an exception
 * is preferred.
 */
export function decrypt(sealed: SealedBytes, key: Uint8Array): Uint8Array | undefined {
  if (key.length !== KEY_BYTES) {
    throw new EncryptionError(
      `secretbox key must be ${KEY_BYTES} bytes, got ${key.length}.`,
      "invalid-key-length"
    );
  }
  if (sealed.length < NONCE_BYTES + TAG_BYTES) {
    return undefined;
  }
  const nonce = sealed.subarray(0, NONCE_BYTES);
  const ciphertext = sealed.subarray(NONCE_BYTES);
  const opened = nacl.secretbox.open(ciphertext, nonce, key);
  return opened ?? undefined;
}

/**
 * Decrypt a sealed blob, throwing {@link EncryptionError} on failure
 * instead of returning undefined.
 */
export function decryptOrThrow(sealed: SealedBytes, key: Uint8Array): Uint8Array {
  const opened = decrypt(sealed, key);
  if (!opened) {
    throw new EncryptionError(
      `Failed to decrypt sealed blob: wrong key, malformed input, or tampered ciphertext.`,
      "decrypt-failed"
    );
  }
  return opened;
}

/**
 * A high-level structured envelope combining encryption with a small
 * amount of metadata the receiver needs to find the right key. The mesh
 * network adapter uses this shape on the wire.
 */
export interface EncryptedEnvelope {
  /** Stable identifier for the document this payload belongs to. The
   * receiver looks this up in its local key store to find the right key. */
  documentId: string;
  /** Sealed blob containing the encrypted payload plus its nonce. */
  sealed: SealedBytes;
}

/**
 * Encrypt a payload and pack it into an {@link EncryptedEnvelope} along
 * with the document id.
 */
export function sealEnvelope(
  payload: Uint8Array,
  documentId: string,
  key: Uint8Array
): EncryptedEnvelope {
  return {
    documentId,
    sealed: encrypt(payload, key),
  };
}

/**
 * Decrypt an {@link EncryptedEnvelope} using the given key. Throws on
 * failure for symmetry with {@link sealEnvelope}.
 */
export function openEnvelope(envelope: EncryptedEnvelope, key: Uint8Array): Uint8Array {
  return decryptOrThrow(envelope.sealed, key);
}

/**
 * Serialise an {@link EncryptedEnvelope} to a single binary blob.
 *
 * Wire format:
 *
 *   [4 bytes BE: documentId byte length]
 *   [N bytes:    documentId UTF-8]
 *   [remaining:  sealed blob (nonce + ciphertext + tag)]
 */
export function encodeEncryptedEnvelope(envelope: EncryptedEnvelope): Uint8Array {
  const idBytes = new TextEncoder().encode(envelope.documentId);
  const out = new Uint8Array(4 + idBytes.length + envelope.sealed.length);
  const view = new DataView(out.buffer);
  view.setUint32(0, idBytes.length, false);
  out.set(idBytes, 4);
  out.set(envelope.sealed, 4 + idBytes.length);
  return out;
}

/**
 * Deserialise a binary envelope produced by {@link encodeEncryptedEnvelope}.
 * Throws on malformed input.
 */
export function decodeEncryptedEnvelope(bytes: Uint8Array): EncryptedEnvelope {
  if (bytes.length < 4) {
    throw new EncryptionError(
      `Encrypted envelope too short: ${bytes.length} bytes.`,
      "envelope-malformed"
    );
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const idLen = view.getUint32(0, false);
  if (bytes.length < 4 + idLen) {
    throw new EncryptionError(
      `Encrypted envelope truncated: declared id length ${idLen}, total ${bytes.length}.`,
      "envelope-malformed"
    );
  }
  const documentId = new TextDecoder().decode(bytes.subarray(4, 4 + idLen));
  const sealed = bytes.slice(4 + idLen);
  return { documentId, sealed };
}
