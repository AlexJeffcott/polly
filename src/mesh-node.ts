/**
 * @fairfox/polly/mesh/node — Node/Bun conveniences for mesh state.
 *
 * The core mesh API (`createMeshClient`, `$meshState`, the keyring storage
 * interface) is runtime-agnostic and ships from `@fairfox/polly/mesh`. This
 * module adds the Node-specific wiring that makes CLIs, cron jobs, and
 * always-on bridges first-class peers on the mesh:
 *
 *   - {@link fileKeyringStorage} — durable, human-inspectable keyring store
 *     backed by `node:fs`. Atomic writes, missing-file returns `null`.
 *   - {@link bootstrapCliKeyring} — wraps {@link fileKeyringStorage} with the
 *     first-run pairing UX described in the RFC: generate an identity if
 *     no keyring exists, print the public-key fingerprint, read a pairing
 *     token from stdin, apply it, and save.
 *   - {@link readPairingTokenFromStdin} — low-level prompt helper for
 *     consumers that want to compose their own bootstrap.
 *
 * What this module deliberately does **not** do: pick a Node WebRTC
 * implementation. `werift` (pure TypeScript, installs everywhere) and
 * `@roamhq/wrtc` (C++ binding, faster DataChannel, platform-dependent
 * binaries) are both valid choices; the consumer `bun add`s whichever fits
 * their deployment and passes the class into `createMeshClient({ rtc })`.
 *
 * @example
 * ```ts
 * import { createMeshClient } from "@fairfox/polly/mesh";
 * import { bootstrapCliKeyring, fileKeyringStorage } from "@fairfox/polly/mesh/node";
 * import { RTCPeerConnection } from "werift";
 *
 * const storage = fileKeyringStorage("./keyring.json");
 * const keyring = await bootstrapCliKeyring({ storage });
 *
 * const client = await createMeshClient({
 *   signaling: { url: "wss://example.com/polly/signaling", peerId: "cli-a1b2" },
 *   rtc:       { RTCPeerConnection },
 *   keyring,
 * });
 * ```
 */

import { readFile, rename, writeFile } from "node:fs/promises";
import { createInterface } from "node:readline/promises";
import {
  deserialiseKeyring,
  type KeyringStorage,
  serialiseKeyring,
} from "./shared/lib/keyring-storage";
import type { MeshKeyring } from "./shared/lib/mesh-network-adapter";
import { applyPairingToken, decodePairingToken } from "./shared/lib/pairing";
import { generateSigningKeyPair } from "./shared/lib/signing";

// Re-export runtime-agnostic pieces so a Node consumer only needs one
// import site.
export type { KeyringStorage } from "./shared/lib/keyring-storage";
export {
  deserialiseKeyring,
  memoryKeyringStorage,
  serialiseKeyring,
} from "./shared/lib/keyring-storage";

/**
 * Filesystem-backed keyring storage. Reads and writes the serialised
 * keyring at {@link path} using the canonical JSON+base64 format. The save
 * path uses a write-to-tmp-then-rename dance so concurrent readers never
 * observe a half-written file; a crash mid-write leaves the previous
 * keyring intact.
 */
export function fileKeyringStorage(path: string): KeyringStorage {
  return {
    load: async () => {
      try {
        const text = await readFile(path, "utf-8");
        return deserialiseKeyring(text);
      } catch (err) {
        if (isFileNotFound(err)) return null;
        throw err;
      }
    },
    save: async (keyring) => {
      const text = serialiseKeyring(keyring);
      const tmp = `${path}.tmp-${process.pid}-${Date.now()}`;
      await writeFile(tmp, text, { mode: 0o600 });
      await rename(tmp, path);
    },
  };
}

/** Options for {@link bootstrapCliKeyring}. */
export interface BootstrapCliKeyringOptions {
  /** Where to persist the keyring. On subsequent runs this file is loaded
   * and returned without prompting. */
  storage: KeyringStorage;
  /** Stream to print pairing prompts to. Defaults to `process.stderr` so
   * pipelines that consume stdout are not polluted. */
  promptStream?: NodeJS.WritableStream;
  /** Stream to read the pairing token from. Defaults to `process.stdin`. */
  inputStream?: NodeJS.ReadableStream;
  /** Override the clock (for tests). Forwarded to {@link applyPairingToken}. */
  now?: () => number;
}

/**
 * First-run-or-return flow for Node CLIs.
 *
 * - If the storage has a keyring saved, load and return it.
 * - Otherwise: generate a fresh Ed25519 identity, print the public-key
 *   fingerprint to `promptStream`, read one line from `inputStream`
 *   (expected to be a base64 pairing token), apply it, save, return.
 *
 * Token *issuance* is deliberately out of scope for this helper — the
 * expected UX is that a trusted device (a browser on the authorising
 * user's laptop) mints the token and the user pastes it into the CLI's
 * stdin. Node processes that need to issue tokens can use
 * {@link createPairingToken} from the main mesh export.
 */
export async function bootstrapCliKeyring(
  options: BootstrapCliKeyringOptions
): Promise<MeshKeyring> {
  const existing = await options.storage.load();
  if (existing !== null) return existing;

  const identity = generateSigningKeyPair();
  const keyring: MeshKeyring = {
    identity,
    knownPeers: new Map(),
    documentKeys: new Map(),
    revokedPeers: new Set(),
  };

  const promptStream = options.promptStream ?? process.stderr;
  const fingerprint = fingerprintPublicKey(identity.publicKey);
  promptStream.write(
    [
      "",
      "Polly mesh-state CLI bootstrap",
      "──────────────────────────────",
      `Fingerprint:  ${fingerprint}`,
      "",
      "Authorise this peer on a trusted device (open the pairing UI, enter",
      "the fingerprint above, copy the generated token). Then paste the",
      "pairing token below and press enter.",
      "",
    ].join("\n")
  );

  const token = await readPairingTokenFromStdin({
    promptStream,
    inputStream: options.inputStream ?? process.stdin,
  });

  const applyOptions = options.now ? { now: options.now } : {};
  applyPairingToken(token, keyring, applyOptions);

  await options.storage.save(keyring);
  promptStream.write(`Pairing applied. Keyring saved.\n`);
  return keyring;
}

/**
 * Prompt for and read a pairing token from a readable stream (stdin by
 * default). Returns the decoded, validated token. Throws
 * {@link PairingError} on malformed input — callers should surface that
 * message to the user and retry.
 */
export async function readPairingTokenFromStdin(
  options: { promptStream?: NodeJS.WritableStream; inputStream?: NodeJS.ReadableStream } = {}
) {
  const rl = createInterface({
    input: options.inputStream ?? process.stdin,
    output: options.promptStream ?? process.stderr,
  });
  try {
    const line = await rl.question("pairing-token> ");
    return decodePairingToken(line.trim());
  } finally {
    rl.close();
  }
}

/** Short, human-readable fingerprint of a public key. */
function fingerprintPublicKey(publicKey: Uint8Array): string {
  // First 8 bytes, hex-encoded, colon-grouped — familiar from SSH.
  const slice = publicKey.slice(0, 8);
  const hex = Array.from(slice)
    .map((b) => b.toString(16).padStart(2, "0"))
    .join("");
  return hex.match(/.{2}/g)?.join(":") ?? hex;
}

function isFileNotFound(err: unknown): boolean {
  return typeof err === "object" && err !== null && "code" in err && err.code === "ENOENT";
}
