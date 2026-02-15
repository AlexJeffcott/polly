// Crypto wrapper - will use WASM module when built
// For now, using Web Crypto API as fallback

export class KeyPair {
  constructor(
    public publicKey: Uint8Array,
    public privateKey: Uint8Array
  ) {}

  static async generate(): Promise<KeyPair> {
    const key = await crypto.subtle.generateKey(
      {
        name: "ECDSA",
        namedCurve: "P-256",
      },
      true,
      ["sign", "verify"]
    );

    const publicKey = await crypto.subtle.exportKey("raw", key.publicKey);
    const privateKey = await crypto.subtle.exportKey("pkcs8", key.privateKey);

    return new KeyPair(new Uint8Array(publicKey), new Uint8Array(privateKey));
  }

  static fromBytes(publicKey: Uint8Array, privateKey: Uint8Array): KeyPair {
    return new KeyPair(publicKey, privateKey);
  }

  toHex(): string {
    return `${bytesToHex(this.publicKey)}:${bytesToHex(this.privateKey)}`;
  }

  static fromHex(hex: string): KeyPair {
    const [pubHex, privHex] = hex.split(":");
    return new KeyPair(hexToBytes(pubHex), hexToBytes(privHex));
  }
}

export async function generateWorkspaceKey(): Promise<Uint8Array> {
  const key = new Uint8Array(32);
  crypto.getRandomValues(key);
  return key;
}

export async function encrypt(data: Uint8Array, key: Uint8Array): Promise<Uint8Array> {
  const cryptoKey = await crypto.subtle.importKey("raw", key, { name: "AES-GCM" }, false, [
    "encrypt",
  ]);

  const iv = crypto.getRandomValues(new Uint8Array(12));
  const encrypted = await crypto.subtle.encrypt({ name: "AES-GCM", iv }, cryptoKey, data);

  // Prepend IV to ciphertext
  const result = new Uint8Array(iv.length + encrypted.byteLength);
  result.set(iv, 0);
  result.set(new Uint8Array(encrypted), iv.length);

  return result;
}

export async function decrypt(encrypted: Uint8Array, key: Uint8Array): Promise<Uint8Array> {
  const cryptoKey = await crypto.subtle.importKey("raw", key, { name: "AES-GCM" }, false, [
    "decrypt",
  ]);

  const iv = encrypted.slice(0, 12);
  const ciphertext = encrypted.slice(12);

  const decrypted = await crypto.subtle.decrypt({ name: "AES-GCM", iv }, cryptoKey, ciphertext);

  return new Uint8Array(decrypted);
}

export async function encryptText(text: string, key: string | Uint8Array): Promise<Uint8Array> {
  const keyBytes = typeof key === "string" ? base64ToBytes(key) : key;
  const encoder = new TextEncoder();
  return encrypt(encoder.encode(text), keyBytes);
}

export async function decryptText(
  encrypted: Uint8Array,
  key: string | Uint8Array
): Promise<string> {
  const keyBytes = typeof key === "string" ? base64ToBytes(key) : key;
  const decrypted = await decrypt(encrypted, keyBytes);
  const decoder = new TextDecoder();
  return decoder.decode(decrypted);
}

// Helper functions
export function bytesToHex(bytes: Uint8Array): string {
  return Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, "0"))
    .join("");
}

export function hexToBytes(hex: string): Uint8Array {
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < hex.length; i += 2) {
    bytes[i / 2] = parseInt(hex.substr(i, 2), 16);
  }
  return bytes;
}

export function bytesToBase64(bytes: Uint8Array): string {
  return btoa(String.fromCharCode(...bytes));
}

export function base64ToBytes(base64: string): Uint8Array {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}
