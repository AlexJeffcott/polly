/**
 * blob-transfer — chunking, reassembly, and wire format for peer-to-peer
 * blob transfer over WebRTC data channels.
 *
 * Blobs are split into fixed-size chunks (64 KiB) and sent as individual
 * data channel messages. The wire format reuses the same length-prefixed
 * header + binary payload layout that MeshWebRTCAdapter uses for Automerge
 * sync messages. Blob messages are distinguished by a `type` field in the
 * JSON header that starts with "blob-".
 *
 * Three message types:
 * - blob-chunk:   a single chunk of a blob transfer
 * - blob-request: ask a peer to send chunks for a specific hash
 * - blob-have:    announce local availability of a blob
 */

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/** Default chunk size in bytes: 64 KiB. Stays well within WebRTC SCTP
 *  message size limits (~256 KiB in most browsers). */
export const BLOB_CHUNK_SIZE = 65_536;

/** High-water mark for RTCDataChannel.bufferedAmount. The sender pauses
 *  when the buffer exceeds this threshold. */
export const BLOB_BUFFER_HIGH_WATER = 256 * 1024;

// ---------------------------------------------------------------------------
// Message header types
// ---------------------------------------------------------------------------

export interface BlobChunkHeader {
  type: "blob-chunk";
  hash: string;
  index: number;
  total: number;
}

export interface BlobRequestHeader {
  type: "blob-request";
  hash: string;
  /** Chunk indices needed. Omit to request all chunks. */
  missing?: number[];
}

export interface BlobHaveHeader {
  type: "blob-have";
  hash: string;
}

export type BlobMessageHeader = BlobChunkHeader | BlobRequestHeader | BlobHaveHeader;

// ---------------------------------------------------------------------------
// Chunking
// ---------------------------------------------------------------------------

/** Split bytes into fixed-size chunks. The last chunk may be smaller. */
export function chunkBlob(bytes: Uint8Array, chunkSize: number = BLOB_CHUNK_SIZE): Uint8Array[] {
  const chunks: Uint8Array[] = [];
  for (let offset = 0; offset < bytes.length; offset += chunkSize) {
    chunks.push(bytes.subarray(offset, Math.min(offset + chunkSize, bytes.length)));
  }
  // An empty blob produces one empty chunk so the protocol always sends
  // at least one blob-chunk message.
  if (chunks.length === 0) {
    chunks.push(new Uint8Array(0));
  }
  return chunks;
}

/** Reassemble chunks into a single Uint8Array. Throws if any chunk index
 *  in [0, total) is missing from the map. */
export function reassembleChunks(chunks: Map<number, Uint8Array>, total: number): Uint8Array {
  let totalBytes = 0;
  for (let i = 0; i < total; i++) {
    const chunk = chunks.get(i);
    if (!chunk) {
      throw new Error(`reassembleChunks: missing chunk ${i} of ${total}`);
    }
    totalBytes += chunk.length;
  }
  const out = new Uint8Array(totalBytes);
  let offset = 0;
  for (let i = 0; i < total; i++) {
    const chunk = chunks.get(i) as Uint8Array;
    out.set(chunk, offset);
    offset += chunk.length;
  }
  return out;
}

/** Return the indices of chunks missing from a partial chunk map. */
export function missingChunkIndices(chunks: Map<number, Uint8Array>, total: number): number[] {
  const missing: number[] = [];
  for (let i = 0; i < total; i++) {
    if (!chunks.has(i)) {
      missing.push(i);
    }
  }
  return missing;
}

// ---------------------------------------------------------------------------
// Wire format
// ---------------------------------------------------------------------------

/** Serialise a blob message into the shared wire format:
 *  [4-byte BE header length][JSON header bytes][binary payload].
 *  Returns an ArrayBuffer-backed Uint8Array usable by RTCDataChannel.send. */
export function serialiseBlobMessage(
  header: BlobMessageHeader,
  data: Uint8Array = new Uint8Array(0)
): Uint8Array<ArrayBuffer> {
  const headerBytes = new TextEncoder().encode(JSON.stringify(header));
  const size = 4 + headerBytes.length + data.length;
  const buffer = new ArrayBuffer(size);
  const out = new Uint8Array(buffer);
  const view = new DataView(buffer);
  view.setUint32(0, headerBytes.length, false);
  out.set(headerBytes, 4);
  out.set(data, 4 + headerBytes.length);
  return out;
}

/** Peek at the header of a wire-format message without full
 *  deserialisation. Returns the parsed header and the data slice,
 *  or undefined if the bytes are too short or malformed. */
export function parseBlobMessage(
  bytes: Uint8Array
): { header: BlobMessageHeader; data: Uint8Array } | undefined {
  if (bytes.length < 4) return undefined;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const headerLen = view.getUint32(0, false);
  if (bytes.length < 4 + headerLen) return undefined;
  try {
    const header = JSON.parse(
      new TextDecoder().decode(bytes.subarray(4, 4 + headerLen))
    ) as BlobMessageHeader;
    const data = bytes.subarray(4 + headerLen);
    return { header, data };
  } catch {
    return undefined;
  }
}

/** Check whether a wire-format message header type starts with "blob-". */
export function isBlobMessageType(bytes: Uint8Array): boolean {
  if (bytes.length < 4) return false;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const headerLen = view.getUint32(0, false);
  if (bytes.length < 4 + headerLen) return false;
  // Fast check: look for "blob-" in the header JSON without full parse.
  // The type field is always near the start of the JSON object.
  const headerSlice = bytes.subarray(4, 4 + headerLen);
  // Search for the byte sequence: "type":"blob-
  const needle = new TextEncoder().encode('"type":"blob-');
  return findSubarray(headerSlice, needle) !== -1;
}

/** Find the first occurrence of needle in haystack. Returns -1 if not found. */
function findSubarray(haystack: Uint8Array, needle: Uint8Array): number {
  if (needle.length === 0) return 0;
  outer: for (let i = 0; i <= haystack.length - needle.length; i++) {
    for (let j = 0; j < needle.length; j++) {
      if (haystack[i + j] !== needle[j]) continue outer;
    }
    return i;
  }
  return -1;
}
