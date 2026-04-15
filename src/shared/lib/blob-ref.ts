/**
 * BlobRef — content-addressed reference to a binary blob.
 *
 * CRDT documents held by `$peerState` and `$meshState` primitives should not embed
 * large binary payloads directly. The Automerge history grows monotonically with every
 * op, and embedding a file means every op carries the file, memory explodes, and sync
 * bandwidth is terrible. The sound pattern is to store a reference to the blob inside
 * the document and keep the bytes in a separate, content-addressed blob store.
 *
 * This module defines the reference shape so that applications can hold `BlobRef`
 * values inside their `$peerState`/`$meshState` documents from day one. The actual
 * blob store, the upload/fetch API, and transport-specific blob sync are deliberately
 * out of scope and will land in a follow-up RFC. Provisioning the type now prevents
 * a data-model migration when that RFC ships.
 *
 * @example
 * ```ts
 * const doc = $peerState<Document>("doc", { title: "", attachments: [] });
 *
 * const bytes = new Uint8Array(await file.arrayBuffer());
 * const ref = await createBlobRef({
 *   bytes,
 *   filename: file.name,
 *   mimeType: file.type,
 * });
 *
 * doc.value = {
 *   ...doc.value,
 *   attachments: [...doc.value.attachments, ref],
 * };
 * ```
 */

/**
 * Content-addressed reference to a binary blob.
 *
 * The `hash` field is a hex-encoded SHA-256 digest of the blob's bytes. Two blobs
 * with identical bytes always produce the same hash, so references can be deduplicated
 * and the blob store (when it ships) can use the hash as its primary key.
 */
export type BlobRef = {
  /** Hex-encoded SHA-256 digest of the blob's bytes (64 lowercase hex characters). */
  hash: string;
  /** Length of the blob in bytes. */
  size: number;
  /** Filename as supplied by the originating application. Not used for addressing. */
  filename: string;
  /** MIME type as supplied by the originating application. Not used for addressing. */
  mimeType: string;
};

/**
 * Type guard for {@link BlobRef}. Useful at CRDT document boundaries where values
 * may have been authored by older clients or by clients running different schemas.
 */
export function isBlobRef(value: unknown): value is BlobRef {
  if (typeof value !== "object" || value === null) return false;
  const v = value as Record<string, unknown>;
  return (
    typeof v["hash"] === "string" &&
    /^[0-9a-f]{64}$/.test(v["hash"]) &&
    typeof v["size"] === "number" &&
    Number.isInteger(v["size"]) &&
    v["size"] >= 0 &&
    typeof v["filename"] === "string" &&
    typeof v["mimeType"] === "string"
  );
}

/**
 * Compute the SHA-256 hex digest of a byte sequence. Pure and deterministic.
 */
export async function computeBlobHash(bytes: Uint8Array): Promise<string> {
  // Copy into a fresh ArrayBuffer-backed view so the buffer type is ArrayBuffer
  // rather than the wider ArrayBufferLike, which crypto.subtle.digest's current
  // type signature rejects for SharedArrayBuffer safety.
  const buffer = new ArrayBuffer(bytes.byteLength);
  const copy = new Uint8Array(buffer);
  copy.set(bytes);
  const digest = await crypto.subtle.digest("SHA-256", buffer);
  const view = new Uint8Array(digest);
  let hex = "";
  for (const byte of view) {
    hex += byte.toString(16).padStart(2, "0");
  }
  return hex;
}

/**
 * Arguments for {@link createBlobRef}.
 */
export type CreateBlobRefArgs = {
  bytes: Uint8Array;
  filename: string;
  mimeType: string;
};

/**
 * Build a {@link BlobRef} from raw bytes and metadata. The hash is computed from the
 * bytes; the filename and mimeType are carried from the originating application
 * verbatim and do not affect the content address.
 */
export async function createBlobRef({
  bytes,
  filename,
  mimeType,
}: CreateBlobRefArgs): Promise<BlobRef> {
  const hash = await computeBlobHash(bytes);
  return {
    hash,
    size: bytes.byteLength,
    filename,
    mimeType,
  };
}
