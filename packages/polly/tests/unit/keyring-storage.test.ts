import { describe, expect, test } from "bun:test";
import {
  deserialiseKeyring,
  memoryKeyringStorage,
  serialiseKeyring,
} from "../../src/shared/lib/keyring-storage";
import type { MeshKeyring } from "../../src/shared/lib/mesh-network-adapter";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";

function makeKeyring(overrides: Partial<MeshKeyring> = {}): MeshKeyring {
  const identity = generateSigningKeyPair();
  return {
    identity,
    knownPeers: new Map([["alice", new Uint8Array([1, 2, 3, 4])]]),
    documentKeys: new Map([["polly-mesh-default", new Uint8Array(32).fill(7)]]),
    revokedPeers: new Set(["mallory"]),
    ...overrides,
  };
}

describe("serialiseKeyring / deserialiseKeyring", () => {
  test("round-trips a minimal keyring", () => {
    const original = makeKeyring();
    const restored = deserialiseKeyring(serialiseKeyring(original));

    expect(restored.identity.publicKey).toEqual(original.identity.publicKey);
    expect(restored.identity.secretKey).toEqual(original.identity.secretKey);
    expect(restored.knownPeers.get("alice")).toEqual(original.knownPeers.get("alice")!);
    expect(restored.documentKeys.get("polly-mesh-default")).toEqual(
      original.documentKeys.get("polly-mesh-default")!
    );
    expect([...restored.revokedPeers]).toEqual([...original.revokedPeers]);
    expect(restored.revocationAuthority).toBeUndefined();
  });

  test("round-trips revocationAuthority when present", () => {
    const original = makeKeyring({ revocationAuthority: new Set(["admin-1", "admin-2"]) });
    const restored = deserialiseKeyring(serialiseKeyring(original));
    expect([...(restored.revocationAuthority ?? [])].sort()).toEqual(["admin-1", "admin-2"]);
  });

  test("skips empty revocationAuthority", () => {
    const original = makeKeyring({ revocationAuthority: new Set() });
    const text = serialiseKeyring(original);
    expect(text.includes("revocationAuthority")).toBe(false);
  });

  test("throws on invalid JSON", () => {
    expect(() => deserialiseKeyring("{not json")).toThrow(/not valid JSON/);
  });

  test("throws when a field has the wrong type instead of coercing it", () => {
    const base = JSON.parse(serialiseKeyring(makeKeyring()));
    const variant = (patch: Record<string, unknown>): string =>
      JSON.stringify({ ...base, ...patch });
    expect(() => deserialiseKeyring(variant({ revokedPeers: "abc" }))).toThrow(/revokedPeers/);
    expect(() => deserialiseKeyring(variant({ revocationAuthority: ["a", 1] }))).toThrow(
      /revocationAuthority/
    );
    expect(() => deserialiseKeyring(variant({ knownPeers: { p: 1 } }))).toThrow(/knownPeers/);
    expect(() => deserialiseKeyring(variant({ documentKeys: "k" }))).toThrow(/documentKeys/);
    expect(() =>
      deserialiseKeyring(variant({ identity: { publicKey: 1, secretKey: "AA==" } }))
    ).toThrow(/identity keys/);
  });

  test("reads absent or null collections as empty", () => {
    const base = JSON.parse(serialiseKeyring(makeKeyring()));
    const text = JSON.stringify({
      version: 1,
      identity: base.identity,
      knownPeers: null,
      revokedPeers: null,
    });
    const keyring = deserialiseKeyring(text);
    expect(keyring.knownPeers.size).toBe(0);
    expect(keyring.documentKeys.size).toBe(0);
    expect(keyring.revokedPeers.size).toBe(0);
    expect(keyring.revocationAuthority).toBeUndefined();
  });

  test("throws on a non-object payload", () => {
    expect(() => deserialiseKeyring("[]")).toThrow(/not an object/);
    expect(() => deserialiseKeyring("null")).toThrow(/not an object/);
  });

  test("throws on wrong version", () => {
    const text = serialiseKeyring(makeKeyring()).replace('"version": 1', '"version": 2');
    expect(() => deserialiseKeyring(text)).toThrow(/unsupported keyring version/);
  });
});

describe("memoryKeyringStorage", () => {
  test("load returns null before save", async () => {
    const storage = memoryKeyringStorage();
    expect(await storage.load()).toBeNull();
  });

  test("round-trips through save/load", async () => {
    const storage = memoryKeyringStorage();
    const keyring = makeKeyring();
    await storage.save(keyring);
    const restored = await storage.load();
    expect(restored).not.toBeNull();
    expect(restored?.identity.publicKey).toEqual(keyring.identity.publicKey);
  });

  test("save replaces prior value", async () => {
    const storage = memoryKeyringStorage();
    const first = makeKeyring();
    const second = makeKeyring();
    await storage.save(first);
    await storage.save(second);
    const restored = await storage.load();
    expect(restored?.identity.publicKey).toEqual(second.identity.publicKey);
    expect(restored?.identity.publicKey).not.toEqual(first.identity.publicKey);
  });
});
