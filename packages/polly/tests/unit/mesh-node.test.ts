import { describe, expect, test } from "bun:test";
import { mkdtempSync, readFileSync } from "node:fs";
import { readdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Readable, Writable } from "node:stream";

import { bootstrapCliKeyring, fileKeyringStorage } from "../../src/mesh-node";
import { deserialiseKeyring } from "../../src/shared/lib/keyring-storage";
import type { MeshKeyring } from "../../src/shared/lib/mesh-network-adapter";
import {
  createPairingTokenWithFreshIdentity,
  encodePairingToken,
} from "../../src/shared/lib/pairing";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";

function tmpDir(): string {
  return mkdtempSync(join(tmpdir(), "polly-mesh-node-"));
}

describe("fileKeyringStorage", () => {
  test("load returns null when file does not exist", async () => {
    const storage = fileKeyringStorage(join(tmpDir(), "keyring.json"));
    expect(await storage.load()).toBeNull();
  });

  test("save writes a readable JSON file", async () => {
    const dir = tmpDir();
    const path = join(dir, "keyring.json");
    const storage = fileKeyringStorage(path);

    const keyring: MeshKeyring = {
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map([["polly-mesh-default", new Uint8Array(32).fill(1)]]),
      revokedPeers: new Set(),
    };
    await storage.save(keyring);

    const text = readFileSync(path, "utf-8");
    expect(text.startsWith("{")).toBe(true);
    const restored = deserialiseKeyring(text);
    expect(restored.identity.publicKey).toEqual(keyring.identity.publicKey);
  });

  test("save is atomic (no .tmp file lingers on success)", async () => {
    const dir = tmpDir();
    const path = join(dir, "keyring.json");
    const storage = fileKeyringStorage(path);
    await storage.save({
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map([["polly-mesh-default", new Uint8Array(32)]]),
      revokedPeers: new Set(),
    });
    const entries = await readdir(dir);
    expect(entries.some((e) => e.endsWith(".tmp"))).toBe(false);
    expect(entries).toContain("keyring.json");
  });

  test("save creates the parent directory when it does not exist", async () => {
    // First-run on a fresh machine: the consumer points
    // fileKeyringStorage at ~/.fairfox/keyring.json and the parent
    // hasn't been created yet. The save should mkdir -p rather than
    // fail at open() on the tmp path.
    const dir = tmpDir();
    const nested = join(dir, "profile", "fairfox", "keyring.json");
    const storage = fileKeyringStorage(nested);
    await storage.save({
      identity: generateSigningKeyPair(),
      knownPeers: new Map(),
      documentKeys: new Map([["polly-mesh-default", new Uint8Array(32)]]),
      revokedPeers: new Set(),
    });
    const reloaded = await storage.load();
    expect(reloaded).not.toBeNull();
  });
});

describe("bootstrapCliKeyring", () => {
  test("returns existing keyring without prompting", async () => {
    const storage = fileKeyringStorage(join(tmpDir(), "keyring.json"));
    const seeded: MeshKeyring = {
      identity: generateSigningKeyPair(),
      knownPeers: new Map([["alice", new Uint8Array([9, 9, 9])]]),
      documentKeys: new Map([["polly-mesh-default", new Uint8Array(32).fill(42)]]),
      revokedPeers: new Set(),
    };
    await storage.save(seeded);

    // stdin closed → if we actually read, the test would hang
    const loaded = await bootstrapCliKeyring({
      storage,
      inputStream: Readable.from([]),
      promptStream: nullWritable(),
    });
    expect(loaded.identity.publicKey).toEqual(seeded.identity.publicKey);
    expect([...loaded.knownPeers.keys()]).toEqual(["alice"]);
  });

  test("first-run generates identity and applies pairing token", async () => {
    const dir = tmpDir();
    const storage = fileKeyringStorage(join(dir, "keyring.json"));

    const { token } = createPairingTokenWithFreshIdentity({
      issuerPeerId: "trusted-device",
      documentKeyId: "polly-mesh-default",
    });
    const encoded = encodePairingToken(token);

    const prompts: string[] = [];
    const keyring = await bootstrapCliKeyring({
      storage,
      inputStream: Readable.from([`${encoded}\n`]),
      promptStream: captureWritable(prompts),
    });

    expect(keyring.identity.publicKey.length).toBe(32);
    expect(keyring.knownPeers.get("trusted-device")).toEqual(token.issuerPublicKey);
    expect(keyring.documentKeys.get("polly-mesh-default")).toEqual(token.documentKey);

    // Verify fingerprint was printed to the prompt stream
    const printed = prompts.join("");
    expect(printed).toMatch(/Fingerprint:\s+[0-9a-f]{2}(:[0-9a-f]{2}){7}/);

    // Second call should load without re-prompting
    const reloaded = await bootstrapCliKeyring({
      storage,
      inputStream: Readable.from([]),
      promptStream: nullWritable(),
    });
    expect(reloaded.identity.publicKey).toEqual(keyring.identity.publicKey);
  });
});

function nullWritable(): NodeJS.WritableStream {
  return new Writable({
    write(_chunk, _enc, cb) {
      cb();
    },
  });
}

function captureWritable(sink: string[]): NodeJS.WritableStream {
  return new Writable({
    write(chunk, _enc, cb) {
      sink.push(chunk.toString("utf-8"));
      cb();
    },
  });
}
