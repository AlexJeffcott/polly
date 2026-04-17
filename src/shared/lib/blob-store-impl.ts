/**
 * blob-store-impl — peer-to-peer blob store backed by WebRTC data channels.
 *
 * The store piggybacks on an existing MeshWebRTCAdapter. Blob messages ride
 * on the same data channel as Automerge sync traffic, distinguished by a
 * "blob-" prefix on the message type field.
 *
 * Lifecycle:
 * - put:  hash-verify → cache plaintext locally → announce blob-have
 * - get:  check cache → if miss, send blob-request(s) → receive chunks
 *         → decrypt each chunk as it arrives → reassemble plaintext
 *         → hash-verify → cache
 *
 * Encryption model: chunk-then-encrypt. The sender chunks the plaintext
 * into 64 KiB pieces, encrypts each chunk independently under the configured
 * key (with a fresh random nonce per chunk), and sends the sealed envelope.
 * The receiver decrypts each chunk on arrival. Peak sender memory is ~1
 * chunk of ciphertext at a time rather than the entire ciphertext blob.
 *
 * Per-op keys: callers can override the store's default encryption key per
 * put/get via BlobTransferOptions.key. This supports per-document keys
 * without requiring the store to track document ownership.
 *
 * Multi-source fetch: the get() flow requests from a single peer initially,
 * but the re-request timer rotates through peers that have announced
 * availability of the blob, so a transfer that stalls on one peer recovers
 * against another.
 */

import { MemoryBlobCache } from "./blob-cache";
import { computeBlobHash } from "./blob-ref";
import type { BlobCache, BlobProgressCallback, BlobStore, BlobStoreOptions } from "./blob-store";
import {
  type BlobChunkHeader,
  type BlobHaveHeader,
  type BlobMessageHeader,
  type BlobRequestHeader,
  chunkBlob,
  missingChunkIndices,
  reassembleChunks,
  serialiseBlobMessage,
} from "./blob-transfer";
import type { MeshWebRTCAdapter } from "./mesh-webrtc-adapter";

const DEFAULT_MAX_BLOB_SIZE = 100 * 1024 * 1024; // 100 MiB
const DOWNLOAD_TIMEOUT_MS = 60_000;
const RE_REQUEST_DELAY_MS = 5_000;

/** State for an in-progress blob download. */
interface DownloadState {
  total: number;
  /** Decrypted plaintext chunks, keyed by index. */
  chunks: Map<number, Uint8Array>;
  resolve: (bytes: Uint8Array) => void;
  reject: (error: Error) => void;
  onProgress?: BlobProgressCallback;
  timeoutId?: ReturnType<typeof setTimeout>;
  reRequestId?: ReturnType<typeof setTimeout>;
  /** Encryption key for this download, if any. */
  key?: Uint8Array;
  /** Peers we've asked, rotated on re-request for multi-source fetch. */
  peersAttempted: string[];
  /** Index into peersAttempted for the next re-request. */
  peerRotationIndex: number;
}

/** Create a blob store that transfers blobs peer-to-peer over a
 *  MeshWebRTCAdapter's data channels. */
export function createBlobStore(adapter: MeshWebRTCAdapter, options?: BlobStoreOptions): BlobStore {
  const maxBlobSize = options?.maxBlobSize ?? DEFAULT_MAX_BLOB_SIZE;
  const defaultKey = options?.encrypt?.key;
  const cache: BlobCache = options?.cache ?? new MemoryBlobCache();

  // Per-hash key used at put time. Retained so that blob-request handlers
  // can encrypt chunks with the same key they were put under.
  const keysByHash = new Map<string, Uint8Array>();
  // Track which peers have which blobs (hash → set of peer IDs).
  const peerBlobs = new Map<string, Set<string>>();
  // Track in-progress downloads (hash → download state).
  const downloads = new Map<string, DownloadState>();
  // Hashes we have locally (for announcing to new peers).
  const localHashes = new Set<string>();
  // Object URL cache (hash → object URL string).
  const urlCache = new Map<string, string>();
  let disposed = false;

  // Wire up the adapter's blob message callback.
  adapter.onBlobMessage = (peerId, header, data) => {
    if (disposed) return;
    const type = header["type"] as string;
    switch (type) {
      case "blob-chunk":
        void handleChunk(peerId, header as unknown as BlobChunkHeader, data);
        break;
      case "blob-request":
        void handleRequest(peerId, header as unknown as BlobRequestHeader);
        break;
      case "blob-have":
        handleHave(peerId, header as unknown as BlobHaveHeader);
        break;
    }
  };

  // Announce local blobs to new peers when they connect.
  const peerCandidateHandler = (event: { peerId: unknown }) => {
    if (disposed) return;
    const newPeerId = event.peerId as unknown as string;
    for (const hash of localHashes) {
      const msg = serialiseBlobMessage({ type: "blob-have", hash } as BlobMessageHeader);
      adapter.sendBlobMessage(newPeerId, msg);
    }
  };
  adapter.on("peer-candidate", peerCandidateHandler);

  // -----------------------------------------------------------------------
  // Crypto helpers
  // -----------------------------------------------------------------------

  async function encryptChunk(plaintext: Uint8Array, key: Uint8Array): Promise<Uint8Array> {
    const { encrypt } = await import("./encryption");
    return encrypt(plaintext, key);
  }

  async function decryptChunk(
    sealed: Uint8Array,
    key: Uint8Array
  ): Promise<Uint8Array | undefined> {
    const { decrypt } = await import("./encryption");
    return decrypt(sealed, key);
  }

  // -----------------------------------------------------------------------
  // Incoming message handlers
  // -----------------------------------------------------------------------

  async function handleChunk(
    peerId: string,
    header: BlobChunkHeader,
    data: Uint8Array
  ): Promise<void> {
    const download = downloads.get(header.hash);
    if (!download) return;
    download.total = header.total;

    // Track this peer as a source of chunks for this blob.
    if (!download.peersAttempted.includes(peerId)) {
      download.peersAttempted.push(peerId);
    }

    // Decrypt if a key is configured.
    let chunkBytes: Uint8Array;
    if (download.key) {
      const plaintext = await decryptChunk(data, download.key);
      if (!plaintext) {
        // Skip this chunk — bad key or corrupted. Let re-request retry.
        return;
      }
      chunkBytes = plaintext;
    } else {
      chunkBytes = data.slice();
    }

    download.chunks.set(header.index, chunkBytes);

    reportChunkProgress(download);
    resetReRequestTimer(download);

    if (download.chunks.size >= header.total) {
      finishDownload(header.hash, download);
    } else {
      scheduleReRequest(header.hash, download);
    }
  }

  function reportChunkProgress(download: DownloadState): void {
    if (!download.onProgress || download.total <= 0) return;
    let loaded = 0;
    for (const chunk of download.chunks.values()) {
      loaded += chunk.length;
    }
    download.onProgress({ loaded, total: undefined, phase: "downloading" });
  }

  function resetReRequestTimer(download: DownloadState): void {
    if (download.reRequestId) {
      clearTimeout(download.reRequestId);
      download.reRequestId = undefined;
    }
  }

  function finishDownload(hash: string, download: DownloadState): void {
    clearDownloadTimers(download);
    try {
      const assembled = reassembleChunks(download.chunks, download.total);
      downloads.delete(hash);
      download.resolve(assembled);
    } catch (err) {
      downloads.delete(hash);
      download.reject(err instanceof Error ? err : new Error(String(err)));
    }
  }

  async function handleRequest(peerId: string, header: BlobRequestHeader): Promise<void> {
    const plaintext = await cache.get(header.hash);
    if (!plaintext) return;

    const plaintextChunks = chunkBlob(plaintext);
    const requested = header.missing ?? plaintextChunks.map((_, i) => i);
    const chunkKey = keysByHash.get(header.hash);

    for (const index of requested) {
      await sendChunkAtIndex(peerId, header.hash, plaintextChunks, index, chunkKey);
    }
  }

  async function sendChunkAtIndex(
    peerId: string,
    hash: string,
    plaintextChunks: Uint8Array[],
    index: number,
    chunkKey: Uint8Array | undefined
  ): Promise<void> {
    if (index < 0 || index >= plaintextChunks.length) return;
    const plainChunk = plaintextChunks[index];
    if (!plainChunk) return;

    const payload = chunkKey ? await encryptChunk(plainChunk, chunkKey) : plainChunk;
    const chunkHeader: BlobChunkHeader = {
      type: "blob-chunk",
      hash,
      index,
      total: plaintextChunks.length,
    };
    const msg = serialiseBlobMessage(chunkHeader as BlobMessageHeader, payload);

    if (!adapter.sendBlobMessage(peerId, msg)) {
      await waitForBufferDrain();
      adapter.sendBlobMessage(peerId, msg);
    }
  }

  function handleHave(peerId: string, header: BlobHaveHeader): void {
    let peers = peerBlobs.get(header.hash);
    if (!peers) {
      peers = new Set();
      peerBlobs.set(header.hash, peers);
    }
    peers.add(peerId);
  }

  // -----------------------------------------------------------------------
  // Helpers
  // -----------------------------------------------------------------------

  function announceHave(hash: string): void {
    const msg = serialiseBlobMessage({ type: "blob-have", hash } as BlobMessageHeader);
    for (const peerId of adapter.connectedPeerIds) {
      adapter.sendBlobMessage(peerId, msg);
    }
  }

  function clearDownloadTimers(download: DownloadState): void {
    if (download.timeoutId) clearTimeout(download.timeoutId);
    if (download.reRequestId) clearTimeout(download.reRequestId);
  }

  function scheduleReRequest(hash: string, download: DownloadState): void {
    download.reRequestId = setTimeout(() => fireReRequest(hash, download), RE_REQUEST_DELAY_MS);
  }

  function fireReRequest(hash: string, download: DownloadState): void {
    if (!downloads.has(hash)) return;
    const missing = missingChunkIndices(download.chunks, download.total);
    if (missing.length === 0) return;

    // Multi-source fetch: rotate through known peers so a stalled
    // transfer recovers against a different source.
    const peers = peerBlobs.get(hash);
    const pool = peers && peers.size > 0 ? Array.from(peers) : Array.from(adapter.connectedPeerIds);
    if (pool.length === 0) return;
    const target = pool[download.peerRotationIndex % pool.length];
    download.peerRotationIndex++;
    if (!target) return;

    const reqHeader: BlobRequestHeader = { type: "blob-request", hash, missing };
    const msg = serialiseBlobMessage(reqHeader as BlobMessageHeader);
    adapter.sendBlobMessage(target, msg);

    // Re-arm timer in case this peer also stalls.
    scheduleReRequest(hash, download);
  }

  function waitForBufferDrain(): Promise<void> {
    return new Promise((resolve) => setTimeout(resolve, 50));
  }

  // -----------------------------------------------------------------------
  // BlobStore implementation
  // -----------------------------------------------------------------------

  const store: BlobStore = {
    async put(ref, bytes, options?): Promise<void> {
      if (disposed) throw new Error("BlobStore is disposed");
      options?.signal?.throwIfAborted();

      if (bytes.length > maxBlobSize) {
        throw new Error(`Blob exceeds maximum size (${bytes.length} > ${maxBlobSize})`);
      }

      // Verify hash.
      const hash = await computeBlobHash(bytes);
      if (hash !== ref.hash) {
        throw new Error(`Hash mismatch: expected ${ref.hash}, got ${hash}`);
      }

      options?.signal?.throwIfAborted();

      // Resolve the encryption key: per-op override > store default > no
      // encryption. Record the key so incoming blob-requests encrypt with
      // the same one.
      const key = options?.key ?? defaultKey;
      if (key) {
        keysByHash.set(ref.hash, key);
      }

      options?.onProgress?.({ loaded: bytes.length, total: bytes.length, phase: "uploading" });

      // Store plaintext in cache. Chunking + encryption is deferred to
      // handleRequest for streaming behavior.
      await cache.put(ref.hash, bytes);
      localHashes.add(ref.hash);

      announceHave(ref.hash);
    },

    async get(hash, options?): Promise<Uint8Array | undefined> {
      if (disposed) throw new Error("BlobStore is disposed");
      options?.signal?.throwIfAborted();

      // Check local cache first.
      const cached = await cache.get(hash);
      if (cached) return cached;

      // Resolve the decryption key: per-op override > store default > no
      // decryption (plaintext chunks).
      const key = options?.key ?? defaultKey;

      // Find peers that have this blob.
      const peers = peerBlobs.get(hash);
      const candidates =
        peers && peers.size > 0 ? Array.from(peers) : Array.from(adapter.connectedPeerIds);
      const targetPeer = candidates[0];
      if (!targetPeer) return undefined;

      const requestHeader: BlobRequestHeader = { type: "blob-request", hash };
      const msg = serialiseBlobMessage(requestHeader as BlobMessageHeader);
      adapter.sendBlobMessage(targetPeer, msg);

      // Wait for chunks to arrive.
      const plaintext = await new Promise<Uint8Array>((resolve, reject) => {
        const download: DownloadState = {
          total: 0,
          chunks: new Map(),
          resolve,
          reject,
          onProgress: options?.onProgress,
          key,
          peersAttempted: [targetPeer],
          peerRotationIndex: 1,
        };
        downloads.set(hash, download);

        options?.signal?.addEventListener(
          "abort",
          () => {
            if (downloads.has(hash)) {
              clearDownloadTimers(download);
              downloads.delete(hash);
              reject(new Error("Blob download aborted"));
            }
          },
          { once: true }
        );

        download.timeoutId = setTimeout(() => {
          if (downloads.has(hash)) {
            clearDownloadTimers(download);
            downloads.delete(hash);
            reject(new Error("Blob download timed out"));
          }
        }, DOWNLOAD_TIMEOUT_MS);
      });

      // Verify hash against the plaintext.
      const actualHash = await computeBlobHash(plaintext);
      if (actualHash !== hash) {
        throw new Error(`Blob hash mismatch after download: expected ${hash}, got ${actualHash}`);
      }

      // Cache locally. Record the key so future blob-requests from peers
      // use the same one.
      await cache.put(hash, plaintext);
      if (key) keysByHash.set(hash, key);
      localHashes.add(hash);

      return plaintext;
    },

    async url(hash): Promise<string | undefined> {
      if (disposed) return undefined;
      const cached = urlCache.get(hash);
      if (cached) return cached;
      const bytes = await cache.get(hash);
      if (!bytes) return undefined;
      const buffer = new ArrayBuffer(bytes.byteLength);
      new Uint8Array(buffer).set(bytes);
      const objectUrl = URL.createObjectURL(new Blob([buffer]));
      urlCache.set(hash, objectUrl);
      return objectUrl;
    },

    async pin(hash): Promise<void> {
      await cache.pin(hash);
    },

    async unpin(hash): Promise<void> {
      await cache.unpin(hash);
    },

    async size(): Promise<number> {
      return cache.size();
    },

    async evict(maxBytes): Promise<number> {
      return cache.evict(maxBytes);
    },

    dispose(): void {
      disposed = true;
      adapter.onBlobMessage = undefined;
      adapter.off("peer-candidate", peerCandidateHandler);
      for (const [hash, download] of downloads) {
        clearDownloadTimers(download);
        download.reject(new Error("BlobStore disposed"));
        downloads.delete(hash);
      }
      for (const objectUrl of urlCache.values()) {
        URL.revokeObjectURL(objectUrl);
      }
      urlCache.clear();
      keysByHash.clear();
      cache.dispose();
    },
  };

  return store;
}
