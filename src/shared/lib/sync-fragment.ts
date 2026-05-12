/**
 * sync-fragment — chunking, reassembly, and wire format for oversized
 * Automerge sync messages sent through MeshWebRTCAdapter.
 *
 * An `RTCDataChannel.send(bytes)` call with a payload above the SCTP
 * `maxMessageSize` limit (256 KiB by default in Chrome and werift) either
 * throws synchronously, drops silently, or stalls the channel — none of
 * which are observable to the caller. A first-connection Automerge sync
 * for a doc whose state exceeds ~200 KiB produces exactly such a message,
 * so without fragmentation the receiver's `dc.onmessage` never fires for
 * the large payload and sync stalls forever.
 *
 * The wire format here mirrors the blob-transfer layout — a 4-byte
 * big-endian header length followed by a JSON header and the chunk
 * payload — but uses a distinct `type` value (`sync-fragment`, no
 * `blob-` prefix) so the existing blob fast-path in MeshWebRTCAdapter
 * does not mistake a sync fragment for a blob chunk.
 */

/** Maximum bytes a single channel.send may carry without fragmentation.
 *  Chosen well below the 256 KiB SCTP cap so the framing header for a
 *  single chunk cannot push the wire frame over the limit. Matches the
 *  blob-transfer chunk size so the two transports have a consistent
 *  per-message footprint on the data channel. */
export const SYNC_FRAGMENT_THRESHOLD = 64 * 1024;

/** Chunk size used when a message exceeds the threshold. */
export const SYNC_FRAGMENT_CHUNK_SIZE = 64 * 1024;

export interface SyncFragmentHeader {
  type: "sync-fragment";
  /** Identifier shared by every fragment of one original message. */
  id: string;
  /** Zero-based fragment index within the message. */
  index: number;
  /** Total number of fragments composing the message. */
  total: number;
}

/** Wire frame for a sync fragment: 4-byte BE header length, JSON header,
 *  raw chunk bytes. Returned as an ArrayBuffer-backed Uint8Array so it is
 *  directly usable by RTCDataChannel.send under strict buffer-source typing. */
export function serialiseSyncFragment(
  header: SyncFragmentHeader,
  data: Uint8Array
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

/** Parse a wire frame produced by {@link serialiseSyncFragment}. Returns
 *  undefined if the bytes are too short, the header is unparseable, or the
 *  header `type` is not `sync-fragment`. */
export function parseSyncFragment(
  bytes: Uint8Array
): { header: SyncFragmentHeader; data: Uint8Array } | undefined {
  if (bytes.length < 4) return undefined;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const headerLen = view.getUint32(0, false);
  if (bytes.length < 4 + headerLen) return undefined;
  try {
    const header = JSON.parse(
      new TextDecoder().decode(bytes.subarray(4, 4 + headerLen))
    ) as SyncFragmentHeader;
    if (header.type !== "sync-fragment") return undefined;
    const data = bytes.subarray(4 + headerLen);
    return { header, data };
  } catch {
    return undefined;
  }
}

/** Cheap probe used on the receive path before parsing — looks for the
 *  literal `"type":"sync-fragment"` byte sequence inside the JSON header
 *  without a full parse. Mirrors `isBlobMessageType`. */
export function isSyncFragmentType(bytes: Uint8Array): boolean {
  if (bytes.length < 4) return false;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const headerLen = view.getUint32(0, false);
  if (bytes.length < 4 + headerLen) return false;
  const headerSlice = bytes.subarray(4, 4 + headerLen);
  const needle = new TextEncoder().encode('"type":"sync-fragment"');
  return findSubarray(headerSlice, needle) !== -1;
}

/** Split a serialised sync message into ordered fragments suitable for
 *  transmission through one data channel. The caller is responsible for
 *  generating the shared `id`. Always returns at least one fragment, so
 *  callers can use it unconditionally without a separate small-message
 *  branch — though MeshWebRTCAdapter shortcuts the small-message case to
 *  avoid the per-chunk header overhead. */
export function chunkSyncMessage(
  bytes: Uint8Array,
  id: string,
  chunkSize: number = SYNC_FRAGMENT_CHUNK_SIZE
): Uint8Array<ArrayBuffer>[] {
  const total = Math.max(1, Math.ceil(bytes.length / chunkSize));
  const fragments: Uint8Array<ArrayBuffer>[] = [];
  for (let index = 0; index < total; index++) {
    const start = index * chunkSize;
    const end = Math.min(start + chunkSize, bytes.length);
    fragments.push(
      serialiseSyncFragment({ type: "sync-fragment", id, index, total }, bytes.subarray(start, end))
    );
  }
  return fragments;
}

/** Reassemble a complete fragment map into the original byte sequence.
 *  Throws if any index in [0, total) is missing. */
export function reassembleSyncFragments(
  chunks: Map<number, Uint8Array>,
  total: number
): Uint8Array {
  let totalBytes = 0;
  for (let i = 0; i < total; i++) {
    const chunk = chunks.get(i);
    if (!chunk) {
      throw new Error(`reassembleSyncFragments: missing fragment ${i} of ${total}`);
    }
    totalBytes += chunk.length;
  }
  const out = new Uint8Array(totalBytes);
  let offset = 0;
  for (let i = 0; i < total; i++) {
    const chunk = chunks.get(i) as unknown as Uint8Array;
    out.set(chunk, offset);
    offset += chunk.length;
  }
  return out;
}

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
