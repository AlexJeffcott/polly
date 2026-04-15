/**
 * revocation — Phase 2 key-revocation flow for $meshState.
 *
 * A $meshState deployment is only as secure as the keys it trusts. When a
 * device is lost, stolen, or compromised, its public key needs to be
 * removed from every other peer's trust set so that any operations signed
 * by that key are refused. This module provides the primitive pieces for
 * that flow: a signed revocation record that names the revoked peer id,
 * carries the issuer's identity, and travels between peers through the
 * same channels as any other signed message.
 *
 * A RevocationRecord is produced by a peer that has decided to revoke
 * another peer (typically because the user told their device to do so).
 * It is then serialised to a binary envelope, broadcast to other peers
 * through whatever transport is available, and applied to each receiving
 * keyring via {@link applyRevocation}. Applying a revocation adds the
 * target peer id to the keyring's {@link MeshKeyring.revokedPeers} set;
 * the MeshNetworkAdapter then drops all further messages from that peer,
 * even though the public key is still present in the knownPeers map.
 *
 * Signature layer: every revocation is signed by the *issuer's* key. The
 * receiver verifies the signature against the issuer's public key before
 * applying. This prevents a peer with no authority from forging a
 * revocation, at least in the signature-level threat model — a compromised
 * peer could still forge revocations naming any other peer, which is why
 * production deployments layer an access-set check on top ("who is
 * authorised to revoke whom"). That layer is a follow-up; the first cut
 * is signature-only, and any signed revocation from a known peer is
 * accepted.
 *
 * Why revocations are signed but not encrypted: revocations are public
 * in the sense that they name "peer X is no longer trusted." There is no
 * confidentiality requirement — anyone seeing a revocation learns only
 * that someone has been kicked out, which is already observable from
 * the absence of their operations. Encrypting them would add cost without
 * adding security, so the wire format is signed-only.
 */

import type { MeshKeyring } from "./mesh-network-adapter";
import {
  decodeSignedEnvelope,
  encodeSignedEnvelope,
  openEnvelope as openSignedEnvelope,
  type SigningKeyPair,
  signEnvelope,
} from "./signing";

/** Current revocation-record format version. */
export const REVOCATION_RECORD_VERSION = 1;

/** Magic header bytes for sanity-checking parsed revocations. ASCII "PRV1". */
export const REVOCATION_MAGIC = new Uint8Array([0x50, 0x52, 0x56, 0x31]);

/**
 * The payload carried inside a signed revocation envelope.
 */
export interface RevocationRecord {
  /** Format version. */
  version: number;
  /** The peer id doing the revoking. Becomes the `senderId` of the signed
   * envelope when the record is serialised. */
  issuerPeerId: string;
  /** The peer id being revoked. After a receiver applies this record, its
   * MeshNetworkAdapter will drop all further messages from this peer. */
  revokedPeerId: string;
  /** Unix timestamp (milliseconds) when the revocation was issued. Carried
   * for audit and for tie-breaking in case an issuer issues multiple
   * revocations targeting the same peer. */
  issuedAt: number;
  /** Optional human-readable reason. Not used by the enforcement layer;
   * applications can surface it in audit logs. */
  reason?: string;
}

/** Errors thrown by the revocation subsystem. */
export class RevocationError extends Error {
  readonly code:
    | "unknown-issuer"
    | "unauthorised-issuer"
    | "signature-invalid"
    | "truncated"
    | "wrong-magic"
    | "unknown-version"
    | "not-signed-by-issuer";

  constructor(message: string, code: RevocationError["code"]) {
    super(message);
    this.name = "RevocationError";
    this.code = code;
  }
}

/** Options for {@link createRevocation}. */
export interface CreateRevocationOptions {
  /** Signing keypair of the issuer. The private key signs the record; the
   * public key is looked up by the receiver via `issuerPeerId`. */
  issuer: SigningKeyPair;
  /** Stable peer id of the issuer. */
  issuerPeerId: string;
  /** Peer id to revoke. */
  revokedPeerId: string;
  /** Optional human-readable reason. */
  reason?: string;
  /** Override the current time. Intended for tests. */
  now?: () => number;
}

/**
 * Build a fresh {@link RevocationRecord}. The returned record is plain
 * data; use {@link encodeRevocation} to wrap it in a signed envelope
 * suitable for transport.
 */
export function createRevocation(options: CreateRevocationOptions): RevocationRecord {
  const now = options.now ? options.now() : Date.now();
  return {
    version: REVOCATION_RECORD_VERSION,
    issuerPeerId: options.issuerPeerId,
    revokedPeerId: options.revokedPeerId,
    issuedAt: now,
    ...(options.reason === undefined ? {} : { reason: options.reason }),
  };
}

/**
 * Apply a verified revocation to a keyring. Mutates the keyring in place:
 * adds the target peer id to {@link MeshKeyring.revokedPeers}. The caller
 * must verify the revocation (via {@link decodeRevocation}) before
 * applying; this function does not revalidate the signature.
 */
export function applyRevocation(record: RevocationRecord, keyring: MeshKeyring): void {
  keyring.revokedPeers.add(record.revokedPeerId);
}

/**
 * Revoke a peer locally without producing a transportable record. Useful
 * for the common case where an application decides to drop a peer on this
 * device without propagating the decision elsewhere (tests, single-device
 * setups). Peers that want the revocation to spread to other devices
 * should use {@link createRevocation} + {@link encodeRevocation}.
 */
export function revokePeerLocally(peerId: string, keyring: MeshKeyring): void {
  keyring.revokedPeers.add(peerId);
}

// ─── binary serialisation ──────────────────────────────────────────────────

/**
 * Serialise a {@link RevocationRecord} to a binary payload ready for
 * signing. The layout is:
 *
 *   [4 bytes: magic "PRV1"]
 *   [1 byte:  version]
 *   [4 bytes BE: issuer id byte length]
 *   [N bytes: issuer id UTF-8]
 *   [4 bytes BE: revoked peer id byte length]
 *   [M bytes: revoked peer id UTF-8]
 *   [8 bytes BE: issuedAt (uint64 milliseconds)]
 *   [4 bytes BE: reason byte length]
 *   [R bytes: reason UTF-8]
 */
function serialiseRevocationPayload(record: RevocationRecord): Uint8Array {
  const issuerBytes = new TextEncoder().encode(record.issuerPeerId);
  const revokedBytes = new TextEncoder().encode(record.revokedPeerId);
  const reasonBytes = new TextEncoder().encode(record.reason ?? "");

  const total =
    REVOCATION_MAGIC.length +
    1 + // version
    4 +
    issuerBytes.length +
    4 +
    revokedBytes.length +
    8 + // issuedAt
    4 +
    reasonBytes.length;

  const out = new Uint8Array(total);
  let offset = 0;

  out.set(REVOCATION_MAGIC, offset);
  offset += REVOCATION_MAGIC.length;

  out[offset] = record.version;
  offset += 1;

  const view = new DataView(out.buffer);
  view.setUint32(offset, issuerBytes.length, false);
  offset += 4;
  out.set(issuerBytes, offset);
  offset += issuerBytes.length;

  view.setUint32(offset, revokedBytes.length, false);
  offset += 4;
  out.set(revokedBytes, offset);
  offset += revokedBytes.length;

  view.setBigUint64(offset, BigInt(record.issuedAt), false);
  offset += 8;

  view.setUint32(offset, reasonBytes.length, false);
  offset += 4;
  out.set(reasonBytes, offset);

  return out;
}

/** Inverse of {@link serialiseRevocationPayload}. */
function parseRevocationPayload(bytes: Uint8Array): RevocationRecord {
  let offset = 0;

  if (bytes.length < REVOCATION_MAGIC.length) {
    throw new RevocationError("Revocation record too short for magic.", "truncated");
  }
  for (let i = 0; i < REVOCATION_MAGIC.length; i++) {
    if (bytes[offset + i] !== REVOCATION_MAGIC[i]) {
      throw new RevocationError("Revocation record magic mismatch.", "wrong-magic");
    }
  }
  offset += REVOCATION_MAGIC.length;

  if (bytes.length < offset + 1) {
    throw new RevocationError("Revocation record truncated at version.", "truncated");
  }
  const version = bytes[offset] as number;
  offset += 1;
  if (version !== REVOCATION_RECORD_VERSION) {
    throw new RevocationError(`Unknown revocation record version: ${version}.`, "unknown-version");
  }

  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);

  if (bytes.length < offset + 4) {
    throw new RevocationError("Revocation record truncated at issuer length.", "truncated");
  }
  const issuerLen = view.getUint32(offset, false);
  offset += 4;
  if (bytes.length < offset + issuerLen) {
    throw new RevocationError("Revocation record truncated at issuer id.", "truncated");
  }
  const issuerPeerId = new TextDecoder().decode(bytes.subarray(offset, offset + issuerLen));
  offset += issuerLen;

  if (bytes.length < offset + 4) {
    throw new RevocationError("Revocation record truncated at revoked id length.", "truncated");
  }
  const revokedLen = view.getUint32(offset, false);
  offset += 4;
  if (bytes.length < offset + revokedLen) {
    throw new RevocationError("Revocation record truncated at revoked id.", "truncated");
  }
  const revokedPeerId = new TextDecoder().decode(bytes.subarray(offset, offset + revokedLen));
  offset += revokedLen;

  if (bytes.length < offset + 8) {
    throw new RevocationError("Revocation record truncated at issuedAt.", "truncated");
  }
  const issuedAt = Number(view.getBigUint64(offset, false));
  offset += 8;

  if (bytes.length < offset + 4) {
    throw new RevocationError("Revocation record truncated at reason length.", "truncated");
  }
  const reasonLen = view.getUint32(offset, false);
  offset += 4;
  if (bytes.length < offset + reasonLen) {
    throw new RevocationError("Revocation record truncated at reason.", "truncated");
  }
  const reason = new TextDecoder().decode(bytes.subarray(offset, offset + reasonLen));
  offset += reasonLen;

  return {
    version,
    issuerPeerId,
    revokedPeerId,
    issuedAt,
    ...(reason ? { reason } : {}),
  };
}

/**
 * Produce a signed, transportable binary blob from a revocation record.
 * Wraps the serialised payload in a {@link SignedEnvelope} signed by the
 * issuer's keypair, then encodes the envelope to bytes.
 */
export function encodeRevocation(record: RevocationRecord, issuer: SigningKeyPair): Uint8Array {
  const payload = serialiseRevocationPayload(record);
  const envelope = signEnvelope(payload, record.issuerPeerId, issuer.secretKey);
  return encodeSignedEnvelope(envelope);
}

/**
 * Parse and verify a signed revocation blob. Returns the decoded record
 * on success; throws {@link RevocationError} on any failure.
 *
 * Verification requires the keyring to already know the issuer's public
 * key (because Polly does not have a global PKI). If the issuer is
 * unknown, the caller receives `unknown-issuer` and can decide whether
 * to cache the revocation for later verification or drop it outright.
 *
 * Authorisation: when the keyring has a non-empty
 * {@link MeshKeyring.revocationAuthority} set, only issuers inside that
 * set can have their revocations accepted. An issuer outside the set
 * produces `unauthorised-issuer`. When the authority set is undefined
 * or empty, any signed revocation from a known peer is accepted — that
 * is the Phase 2 first-cut default, preserved for backward compatibility.
 */
export function decodeRevocation(bytes: Uint8Array, keyring: MeshKeyring): RevocationRecord {
  const envelope = decodeSignedEnvelope(bytes);
  const issuerKey = keyring.knownPeers.get(envelope.senderId);
  if (!issuerKey) {
    throw new RevocationError(
      `Revocation issuer ${envelope.senderId} is not in the local keyring.`,
      "unknown-issuer"
    );
  }
  if (
    keyring.revocationAuthority !== undefined &&
    keyring.revocationAuthority.size > 0 &&
    !keyring.revocationAuthority.has(envelope.senderId)
  ) {
    throw new RevocationError(
      `Revocation issuer ${envelope.senderId} is not in the keyring's revocation authority set.`,
      "unauthorised-issuer"
    );
  }
  let payloadBytes: Uint8Array;
  try {
    payloadBytes = openSignedEnvelope(envelope, issuerKey);
  } catch {
    throw new RevocationError(
      `Revocation signature failed verification for issuer ${envelope.senderId}.`,
      "signature-invalid"
    );
  }

  const record = parseRevocationPayload(payloadBytes);
  // Paranoid cross-check: the payload's claimed issuer must match the
  // envelope's authenticated sender. Mismatch means a forged payload.
  if (record.issuerPeerId !== envelope.senderId) {
    throw new RevocationError(
      `Revocation payload claims issuer ${record.issuerPeerId} but the envelope was signed by ${envelope.senderId}.`,
      "not-signed-by-issuer"
    );
  }
  return record;
}
