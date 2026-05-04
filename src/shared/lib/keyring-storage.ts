/**
 * keyring-storage — persistence abstraction for {@link MeshKeyring}.
 *
 * The keyring itself is a plain structural object of `Map`s, `Set`s, and a
 * signing keypair; it is deliberately not coupled to any persistence layer.
 * This module defines a storage interface that applications implement once
 * for their runtime (IndexedDB, the filesystem, a keychain, a secret
 * manager, whatever) and wire into {@link createMeshClient} via its
 * `keyring.storage` option.
 *
 * A canonical JSON-with-base64 serialisation is provided by
 * {@link serialiseKeyring} and {@link deserialiseKeyring}. It is inspectable
 * by humans, survives manual edits, and round-trips every field of the
 * keyring. Storage implementations that write plain strings (files,
 * localStorage, `kv` stores) can lean on these helpers; storage
 * implementations that persist structured data (IndexedDB, a keychain API)
 * can serialise differently if they prefer.
 */

import type { MeshKeyring } from "./mesh-network-adapter";
import type { SigningKeyPair } from "./signing";

/**
 * A load/save pair for a single {@link MeshKeyring}. Implementations are
 * free to choose where and how the keyring is stored; the factory only
 * cares that `load()` returns the previously-saved keyring or `null`, and
 * that `save(keyring)` durably persists it.
 */
export interface KeyringStorage {
  /** Load the previously-saved keyring, or return `null` if none exists.
   * Implementations may throw for truly exceptional conditions (disk
   * errors, permission failures); a missing keyring is not exceptional. */
  load(): Promise<MeshKeyring | null>;
  /** Durably persist the keyring. Implementations should atomically replace
   * any existing stored value; partial writes must not leave the store in
   * an inconsistent state. */
  save(keyring: MeshKeyring): Promise<void>;
}

/**
 * In-memory storage. Useful for tests, ephemeral tools, and the first-run
 * bootstrap path where the keyring only lives for the duration of the
 * process. Calling `save` holds the keyring in a closed-over variable;
 * `load` returns it on subsequent calls within the same process.
 */
export function memoryKeyringStorage(): KeyringStorage {
  let stored: MeshKeyring | null = null;
  return {
    load: async () => stored,
    save: async (keyring) => {
      stored = keyring;
    },
  };
}

// ─── Canonical JSON+base64 serialisation ───────────────────────────────────

interface SerialisedKeyring {
  version: 1;
  identity: { publicKey: string; secretKey: string };
  knownPeers: Record<string, string>;
  documentKeys: Record<string, string>;
  revokedPeers: string[];
  revocationAuthority?: string[];
}

/**
 * Encode a {@link MeshKeyring} to a canonical JSON string. Every
 * `Uint8Array` field (identity keys, public keys, document keys) is
 * base64-encoded; `Map`s and `Set`s become plain objects and arrays. The
 * output is pretty-printed so a human operator can eyeball or hand-edit
 * the file on disk.
 */
export function serialiseKeyring(keyring: MeshKeyring): string {
  const payload: SerialisedKeyring = {
    version: 1,
    identity: {
      publicKey: bytesToBase64(keyring.identity.publicKey),
      secretKey: bytesToBase64(keyring.identity.secretKey),
    },
    knownPeers: mapToBase64Record(keyring.knownPeers),
    documentKeys: mapToBase64Record(keyring.documentKeys),
    revokedPeers: [...keyring.revokedPeers],
  };
  if (keyring.revocationAuthority && keyring.revocationAuthority.size > 0) {
    payload.revocationAuthority = [...keyring.revocationAuthority];
  }
  return JSON.stringify(payload, null, 2);
}

/**
 * Decode a keyring from the format produced by {@link serialiseKeyring}.
 * Throws with a descriptive message when the input is malformed, so
 * corrupt storage surfaces as an actionable error rather than a silent
 * downgrade.
 */
export function deserialiseKeyring(text: string): MeshKeyring {
  let raw: unknown;
  try {
    raw = JSON.parse(text);
  } catch (err) {
    throw new Error(`KeyringStorage: keyring payload is not valid JSON: ${(err as Error).message}`);
  }
  if (!raw || typeof raw !== "object") {
    throw new Error("KeyringStorage: keyring payload is not an object");
  }
  const r = raw as unknown as Partial<SerialisedKeyring>;
  if (r.version !== 1) {
    throw new Error(`KeyringStorage: unsupported keyring version: ${String(r.version)}`);
  }
  if (!r.identity || typeof r.identity !== "object") {
    throw new Error("KeyringStorage: keyring payload is missing identity");
  }
  const identity: SigningKeyPair = {
    publicKey: base64ToBytes(r.identity.publicKey),
    secretKey: base64ToBytes(r.identity.secretKey),
  };
  const keyring: MeshKeyring = {
    identity,
    knownPeers: base64RecordToMap(r.knownPeers ?? {}),
    documentKeys: base64RecordToMap(r.documentKeys ?? {}),
    revokedPeers: new Set(r.revokedPeers ?? []),
  };
  if (r.revocationAuthority && r.revocationAuthority.length > 0) {
    keyring.revocationAuthority = new Set(r.revocationAuthority);
  }
  return keyring;
}

function mapToBase64Record(map: Map<string, Uint8Array>): Record<string, string> {
  const out: Record<string, string> = {};
  for (const [key, value] of map) {
    out[key] = bytesToBase64(value);
  }
  return out;
}

function base64RecordToMap(record: Record<string, string>): Map<string, Uint8Array> {
  const out = new Map<string, Uint8Array>();
  for (const [key, value] of Object.entries(record)) {
    out.set(key, base64ToBytes(value));
  }
  return out;
}

function bytesToBase64(bytes: Uint8Array): string {
  // btoa is available in browsers, Node 16+, and Bun.
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary);
}

function base64ToBytes(b64: string): Uint8Array {
  const binary = atob(b64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}
