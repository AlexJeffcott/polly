// Tests for client-side cryptography functions
import { describe, expect, test } from "bun:test";
import {
  base64ToBytes,
  bytesToBase64,
  bytesToHex,
  decryptText,
  encryptText,
  hexToBytes,
  KeyPair,
} from "../src/crypto";

describe("Base64 Encoding/Decoding", () => {
  test("encodes bytes to base64", () => {
    const bytes = new Uint8Array([72, 101, 108, 108, 111]); // "Hello"
    const encoded = bytesToBase64(bytes);
    expect(typeof encoded).toBe("string");
    expect(encoded).toBe("SGVsbG8=");
  });

  test("decodes base64 to bytes", () => {
    const encoded = "SGVsbG8=";
    const bytes = base64ToBytes(encoded);
    expect(bytes).toBeInstanceOf(Uint8Array);
    expect(Array.from(bytes)).toEqual([72, 101, 108, 108, 111]);
  });

  test("roundtrip encoding/decoding", () => {
    const original = new Uint8Array([1, 2, 3, 4, 5, 255, 0, 128]);
    const encoded = bytesToBase64(original);
    const decoded = base64ToBytes(encoded);
    expect(Array.from(decoded)).toEqual(Array.from(original));
  });
});

describe("Hex Encoding/Decoding", () => {
  test("encodes bytes to hex", () => {
    const bytes = new Uint8Array([15, 255, 0, 128]);
    const hex = bytesToHex(bytes);
    expect(hex).toBe("0fff0080");
  });

  test("decodes hex to bytes", () => {
    const hex = "0fff0080";
    const bytes = hexToBytes(hex);
    expect(Array.from(bytes)).toEqual([15, 255, 0, 128]);
  });

  test("handles uppercase hex", () => {
    const hex = "0FFF0080";
    const bytes = hexToBytes(hex);
    expect(Array.from(bytes)).toEqual([15, 255, 0, 128]);
  });

  test("roundtrip encoding/decoding", () => {
    const original = new Uint8Array([1, 2, 3, 4, 5, 255, 0, 128]);
    const hex = bytesToHex(original);
    const decoded = hexToBytes(hex);
    expect(Array.from(decoded)).toEqual(Array.from(original));
  });
});

describe("KeyPair Generation", () => {
  test("generates a keypair", async () => {
    const keypair = await KeyPair.generate();
    expect(keypair).toBeDefined();
    expect(keypair.publicKey).toBeInstanceOf(Uint8Array);
    expect(keypair.privateKey).toBeInstanceOf(Uint8Array);
    expect(keypair.publicKey.length).toBeGreaterThan(0);
    expect(keypair.privateKey.length).toBeGreaterThan(0);
  });

  test("generates different keypairs each time", async () => {
    const keypair1 = await KeyPair.generate();
    const keypair2 = await KeyPair.generate();

    const hex1 = bytesToHex(keypair1.publicKey);
    const hex2 = bytesToHex(keypair2.publicKey);

    expect(hex1).not.toBe(hex2);
  });
});

describe("Encryption/Decryption", () => {
  test("encrypts and decrypts text", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32)); // 256-bit key
    const plaintext = "Hello, World!";

    const encrypted = await encryptText(plaintext, key);
    const decrypted = await decryptText(encrypted, key);

    expect(decrypted).toBe(plaintext);
  });

  test("encrypted text differs from plaintext", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "Secret message";

    const encrypted = await encryptText(plaintext, key);
    const encryptedBase64 = bytesToBase64(encrypted);

    expect(encryptedBase64).not.toContain(plaintext);
  });

  test("different encryptions of same text are different (due to nonce)", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "Same text";

    const encrypted1 = await encryptText(plaintext, key);
    const encrypted2 = await encryptText(plaintext, key);

    expect(bytesToBase64(encrypted1)).not.toBe(bytesToBase64(encrypted2));

    // But both decrypt to same plaintext
    const decrypted1 = await decryptText(encrypted1, key);
    const decrypted2 = await decryptText(encrypted2, key);

    expect(decrypted1).toBe(plaintext);
    expect(decrypted2).toBe(plaintext);
  });

  test("decryption with wrong key fails", async () => {
    const key1 = crypto.getRandomValues(new Uint8Array(32));
    const key2 = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "Secret";

    const encrypted = await encryptText(plaintext, key1);

    await expect(decryptText(encrypted, key2)).rejects.toThrow();
  });

  test("handles empty string", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "";

    const encrypted = await encryptText(plaintext, key);
    const decrypted = await decryptText(encrypted, key);

    expect(decrypted).toBe(plaintext);
  });

  test("handles unicode characters", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "Hello 世界 🌍 café";

    const encrypted = await encryptText(plaintext, key);
    const decrypted = await decryptText(encrypted, key);

    expect(decrypted).toBe(plaintext);
  });

  test("handles large text", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const plaintext = "A".repeat(10000); // 10KB

    const encrypted = await encryptText(plaintext, key);
    const decrypted = await decryptText(encrypted, key);

    expect(decrypted).toBe(plaintext);
  });

  test("handles JSON serialization", async () => {
    const key = crypto.getRandomValues(new Uint8Array(32));
    const data = {
      id: "task-123",
      text: "Buy milk",
      priority: "high",
      nested: { foo: "bar" },
    };
    const plaintext = JSON.stringify(data);

    const encrypted = await encryptText(plaintext, key);
    const decrypted = await decryptText(encrypted, key);
    const parsed = JSON.parse(decrypted);

    expect(parsed).toEqual(data);
  });
});
