/**
 * blob-store — types and interfaces for Polly's content-addressed blob storage.
 *
 * This file contains only type definitions and interfaces. It has no runtime
 * imports from tweetnacl or other crypto libraries, so peer-only consumers
 * tree-shake cleanly when importing from @fairfox/polly/mesh.
 */

import type { BlobRef } from "./blob-ref";

// ---------------------------------------------------------------------------
// Progress reporting
// ---------------------------------------------------------------------------

export type BlobProgressPhase = "encrypting" | "uploading" | "downloading" | "decrypting";

export interface BlobProgressEvent {
  /** Bytes processed so far in the current phase. */
  loaded: number;
  /** Total bytes expected. Undefined when unknown (e.g. start of download). */
  total: number | undefined;
  /** Current operation phase. */
  phase: BlobProgressPhase;
}

export type BlobProgressCallback = (event: BlobProgressEvent) => void;

export interface BlobTransferOptions {
  onProgress?: BlobProgressCallback;
  signal?: AbortSignal;
  /** Override the store's default encryption key for this operation.
   *  Useful for per-document keys: pass the document's key here so the
   *  blob is encrypted under that key rather than the store default.
   *  Ignored if the store has no encryption configured. */
  key?: Uint8Array;
}

// ---------------------------------------------------------------------------
// Cache abstraction
// ---------------------------------------------------------------------------

/** Storage backend for blob bytes. Implementations must store Uint8Array
 *  values keyed by SHA-256 hex hash without serialisation loss. */
export interface BlobCache {
  get(hash: string): Promise<Uint8Array | undefined>;
  put(hash: string, bytes: Uint8Array): Promise<void>;
  has(hash: string): Promise<boolean>;
  delete(hash: string): Promise<void>;
  dispose(): void;

  /** Mark a hash as pinned — it will not be evicted until unpinned.
   *  Applications typically pin blobs referenced by documents they
   *  currently hold locally. */
  pin(hash: string): Promise<void>;

  /** Remove the pinned mark. The blob becomes eligible for eviction. */
  unpin(hash: string): Promise<void>;

  /** Total bytes stored in the cache. */
  size(): Promise<number>;

  /** Evict unpinned entries in LRU order until total size ≤ maxBytes.
   *  Returns the number of bytes freed. */
  evict(maxBytes: number): Promise<number>;
}

// ---------------------------------------------------------------------------
// Blob store
// ---------------------------------------------------------------------------

export interface BlobStore {
  /** Store bytes locally and announce availability to connected peers.
   *  Verifies that the hash of `bytes` matches `ref.hash` before storing. */
  put(ref: BlobRef, bytes: Uint8Array, options?: BlobTransferOptions): Promise<void>;

  /** Retrieve bytes by hash. Checks local cache first; if not cached,
   *  requests from connected peers. Returns undefined if unavailable. */
  get(hash: string, options?: BlobTransferOptions): Promise<Uint8Array | undefined>;

  /** Return an object URL for rendering (e.g. <img src>). Cached per hash;
   *  repeated calls with the same hash return the same URL. Returns
   *  undefined if the blob is not in the local cache. All URLs are revoked
   *  on dispose(). */
  url(hash: string): Promise<string | undefined>;

  /** Pin a blob so it won't be evicted. Applications should pin blobs
   *  referenced by documents they currently hold. */
  pin(hash: string): Promise<void>;

  /** Unpin a blob. Removing a document that references a blob is a
   *  natural place to unpin. */
  unpin(hash: string): Promise<void>;

  /** Total bytes stored in the local cache. */
  size(): Promise<number>;

  /** Evict unpinned entries in LRU order until total size ≤ maxBytes.
   *  Returns bytes freed. */
  evict(maxBytes: number): Promise<number>;

  /** Revoke all outstanding object URLs and release resources. */
  dispose(): void;
}

// ---------------------------------------------------------------------------
// Blob store options
// ---------------------------------------------------------------------------

export interface BlobStoreOptions {
  /** Maximum blob size in bytes. Defaults to 100 MiB. */
  maxBlobSize?: number;
  /** Default encryption config. When configured, blobs are encrypted
   *  with this key unless overridden per-op via BlobTransferOptions.key.
   *  Omit for plaintext transfer (DTLS only). */
  encrypt?: { key: Uint8Array };
  /** Custom cache implementation. Defaults to MemoryBlobCache (suitable
   *  for tests and Node). Browser consumers should pass an
   *  IndexedDBBlobCache instance. */
  cache?: BlobCache;
}
