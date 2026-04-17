# RFC-042 — Blob storage and large-file sync for Polly

Tracking issue: TBD

Status: draft design for the blob storage and large-file sync primitive referenced as "the follow-up RFC" in [RFC-041-peer-first.md](./RFC-041-peer-first.md) and [RFC-041-peer-first-webrtc.md](./RFC-041-peer-first-webrtc.md). This RFC builds on the `BlobRef` type already shipped in `src/shared/lib/blob-ref.ts` and designs the machinery that makes the reference useful: a blob store, a transfer protocol, and a lifecycle.

## The question worth answering

CRDT documents should not hold binary payloads. The Automerge history grows monotonically with every operation, and embedding a file means every sync carries the file, memory explodes, and bandwidth is terrible. Polly already knows this — `BlobRef` exists precisely to separate the reference from the bytes — but a reference without a store is a promise without a mechanism. The developer who writes `attachments: [...doc.value.attachments, ref]` today has done the correct thing for data modelling and has no way to make it work at runtime.

The question is: what does Polly provide so that `BlobRef` values in documents become live references that resolve to bytes, transfer between peers, respect the transport's trust model, and clean up after themselves?

The answer is peer-to-peer. Blobs transfer directly between clients over WebRTC data channels — the same connections that `$meshState` already establishes. No server stores blob bytes. No server serves blob bytes. The Polly server stays exactly as it is today: a thin relay for `$sharedState` messages, an Automerge sync peer for `$peerState` documents, and a stateless signalling endpoint for `$meshState` connections. Blob storage is a client-side concern backed by a content-addressed cache in IndexedDB, with bytes flowing peer-to-peer when a client needs a blob it does not yet have.

This design eliminates the operational surface that server-side blob storage would introduce: no object storage, no disk management, no garbage collection, no durability story for flat files. The server's responsibility is document metadata — small, text-shaped, well-served by Automerge and Litestream. Binary payloads are a different kind of data with a different lifecycle, and keeping them off the server is the architecturally honest decision.

## Blobs are a mesh-infrastructure feature

Blob transfer requires direct peer-to-peer connections. Those connections come from the mesh layer — the `MeshWebRTCAdapter` that `$meshState` uses for all its traffic. Applications that use `$meshState` already have this infrastructure. Applications that use only `$peerState` and want blob support must add mesh infrastructure (a signalling server and WebRTC adapter) for blob transfer, even if they do not use `$meshState` for document sync.

This is a reasonable ask. It says: if you want peer-to-peer file transfer, you need peer-to-peer connections. The signalling server is small and stateless; the WebRTC adapter is already built. Adding them to a `$peerState`-only application is a configuration decision, not a new dependency.

`$sharedState` does not participate in blob storage. It has no CRDT sync layer and therefore no document to anchor a `BlobRef` lifecycle to.

## What the developer writes

```typescript
import { createBlobStore } from "@fairfox/polly/mesh";

const blobs = createBlobStore(meshAdapter);
```

One factory, one blob store, one transport. The `meshAdapter` is a `MeshWebRTCAdapter` instance — the same adapter the application already uses for `$meshState`, or one created specifically for blob transfer if the application uses only `$peerState`.

Storing a blob:

```typescript
const file = inputElement.files[0];
const bytes = new Uint8Array(await file.arrayBuffer());
const ref = await createBlobRef({
  bytes,
  filename: file.name,
  mimeType: file.type,
});
await blobs.put(ref, bytes);
// embed the ref in a document
doc.value = { ...doc.value, avatar: ref };
```

`put` stores the bytes in the local IndexedDB cache and makes them available for transfer to peers that request them. It verifies the hash before storing. If a blob with the same hash already exists locally, it returns immediately.

Fetching a blob:

```typescript
const bytes = await blobs.get(ref.hash);
```

`get` checks the local cache first. If the blob is not cached, it requests it from connected peers over the WebRTC data channel. The first peer that has the blob sends it in chunks; the receiver reassembles, decrypts (for `$meshState` documents), verifies the SHA-256 hash against the `BlobRef`, and caches the result locally.

Rendering a blob:

```typescript
const objectUrl = await blobs.url(ref.hash);
// use in <img src={objectUrl}> or <a href={objectUrl}>
```

`url` returns an object URL backed by the local cache. The store caches object URLs per hash — repeated calls with the same hash return the same URL without creating a new one. All outstanding object URLs are revoked when `dispose()` is called.

Progress and cancellation:

```typescript
await blobs.put(ref, bytes, {
  onProgress: (event) => {
    // event.loaded, event.total, event.phase: "uploading" | "encrypting"
  },
  signal: abortController.signal,
});

const bytes = await blobs.get(ref.hash, {
  onProgress: (event) => {
    // event.loaded, event.total, event.phase: "downloading" | "decrypting"
  },
  signal: abortController.signal,
});
```

`AbortSignal` cancels in-flight transfers. Progress reports `loaded` and `total` bytes; `total` is `undefined` when unknown (e.g. the first moments of a download before the sender reports the blob size). The `phase` discriminator tells the UI what the store is doing. SHA-256 hashing is fast enough at the maximum blob size (100 MiB hashes in ~100ms in WebCrypto) that it does not warrant its own progress phase.

That is the entire API. One store, four methods: `put`, `get`, `url`, `dispose`.

## Type signatures

The blob store types live in `src/shared/lib/blob-store.ts`, separate from any file that imports `tweetnacl`, so that peer-only consumers tree-shake cleanly.

```typescript
import type { BlobRef } from "./blob-ref";

export type BlobProgressPhase =
  | "encrypting"
  | "uploading"
  | "downloading"
  | "decrypting";

export interface BlobProgressEvent {
  loaded: number;
  total: number | undefined;
  phase: BlobProgressPhase;
}

export type BlobProgressCallback = (event: BlobProgressEvent) => void;

export interface BlobTransferOptions {
  onProgress?: BlobProgressCallback;
  signal?: AbortSignal;
}

export interface BlobStore {
  put(ref: BlobRef, bytes: Uint8Array, options?: BlobTransferOptions): Promise<void>;
  get(hash: string, options?: BlobTransferOptions): Promise<Uint8Array | undefined>;
  url(hash: string): Promise<string | undefined>;
  dispose(): void;
}
```

`put` takes a `BlobRef` and the bytes. The ref is created beforehand via `createBlobRef` (already shipped in `blob-ref.ts`). The store verifies that the hash of the bytes matches `ref.hash` before storing — it does not trust the caller to have computed the hash correctly.

`get` takes a hash string, not a full `BlobRef`, because the caller may have the hash from a document field without having constructed a full `BlobRef` object. It returns `undefined` if the blob is unavailable (not cached locally and no connected peer has it).

`url` is `async` because it may need to read from IndexedDB before creating an object URL. It returns `undefined` if the blob is not cached.

`dispose` revokes all outstanding object URLs and releases resources.

## Encryption

Blobs referenced by `$meshState` documents are encrypted before transfer. Blobs referenced by `$peerState` documents are not — DTLS on the WebRTC data channel provides transport encryption, and `$peerState`'s trust model already assumes the infrastructure can see document contents.

Encryption uses the existing `encrypt` and `decrypt` functions from `src/shared/lib/encryption.ts` (XSalsa20-Poly1305 via tweetnacl). The default encryption key comes from the store's `encrypt.key` option. Callers can override the key per operation via `BlobTransferOptions.key`, which supports per-document keys without requiring the store to track document ownership — the application knows which document a blob belongs to and passes the corresponding key on every `put` and `get`.

The encryption order is chunk-then-encrypt. The sender chunks the plaintext into 64 KiB pieces first, then encrypts each chunk independently with a fresh random nonce. Each chunk arrives as a standalone sealed envelope (24-byte nonce + ciphertext + 16-byte Poly1305 MAC) and is decrypted as soon as it reaches the receiver. The receiver reassembles the decrypted plaintext chunks and verifies the SHA-256 against the `BlobRef.hash`.

Peak sender memory is one chunk of ciphertext at a time — roughly 64 KiB of working data plus whatever the application already held in plaintext. Encrypt-then-chunk would have forced the sender to hold both the full plaintext and full ciphertext simultaneously (~200 MiB for a 100 MiB blob); chunk-then-encrypt keeps working memory bounded. The per-chunk overhead (40 bytes for nonce + MAC) is 0.06% at 64 KiB chunks.

Each chunk is independently authenticated. A tampered or corrupted chunk fails Poly1305 verification immediately and is dropped by the receiver, which lets the re-request timer pull a replacement from a different peer. The `BlobRef.hash` covers the plaintext (not ciphertext), so the same logical blob encrypted under different keys or nonces still deduplicates by content address.

## Transfer protocol

Blobs transfer over the same WebRTC data channel that carries Automerge sync messages. The existing wire format (`MeshWebRTCAdapter`, `mesh-webrtc-adapter.ts:358-378`) is `[4-byte header length][JSON header][binary payload]`. Blob traffic is distinguished from Automerge sync traffic by a `type` field in the JSON header.

Three message types:

```typescript
// Sent by receiver to request a blob from a peer
interface BlobRequestHeader {
  type: "blob-request";
  hash: string;
  missing?: number[];  // chunk indices needed; omit to request all
}

// Sent by sender, one per chunk
interface BlobChunkHeader {
  type: "blob-chunk";
  hash: string;
  index: number;       // 0-based chunk index
  total: number;       // total chunk count
}

// Sent by a peer to announce it has a blob available
interface BlobHaveHeader {
  type: "blob-have";
  hash: string;
}
```

The binary payload of a `blob-chunk` message is either a plaintext chunk (unencrypted transfers) or a sealed envelope — `nonce (24) | ciphertext | MAC (16)` — produced by `encrypt(plaintextChunk, key)` for encrypted transfers. Each chunk is independently decryptable; receivers decrypt as chunks arrive rather than waiting for reassembly.

**Chunk size.** Fixed at 64 KiB. This stays well within WebRTC SCTP message size limits (~256 KiB in most browsers), avoids SCTP-level fragmentation, and provides fine-grained progress reporting. A 100 MiB blob produces ~1,600 chunks.

**Dispatch.** The `dispatchMessage` method in `MeshWebRTCAdapter` (`mesh-webrtc-adapter.ts:341`) peeks at the JSON header's `type` field. Messages with `type: "blob-chunk"`, `"blob-request"`, or `"blob-have"` are emitted as blob events. All other messages (Automerge sync) flow through the existing `deserialiseMessage` path unchanged.

**Flow control.** The sender checks `RTCDataChannel.bufferedAmount` before sending each chunk and pauses when it exceeds a high-water mark (default 256 KiB). It resumes when `bufferedamountlow` fires. This prevents blob transfers from starving Automerge sync traffic on the shared channel.

**Integrity.** Transport-level integrity is provided by DTLS on every WebRTC SCTP message. End-to-end integrity is provided by SHA-256 verification on the reassembled blob (the hash in the `BlobRef`). Per-chunk CRC-32 is unnecessary — DTLS handles transport integrity and SHA-256 handles authentication. Adding a per-chunk checksum on top would be belt-and-suspenders redundancy with measurable CPU cost per chunk and no failure mode it catches that the other two layers miss.

**Resumption and multi-source fetch.** If chunks stop arriving for longer than a configurable timeout (default 5 seconds), the receiver fires a re-request for the missing chunk indices. Each re-request rotates to a different peer that has announced availability of the blob, so a transfer that stalls on one source recovers against another. The original sender may still complete and send any chunks it had in flight; duplicates are silently dropped because each chunk is content-addressed by (hash, index). Once the download completes across any combination of peers, the reassembled plaintext is hashed and verified against the `BlobRef.hash`.

**Announcement.** When a peer receives a document update (via Automerge sync) that contains a new `BlobRef`, and it does not have the blob locally, it sends a `blob-request` to the peer that sent the document update. If that peer does not have the blob either (it received the document from a third peer), it responds with nothing and the receiver tries other connected peers. A peer that completes a blob download sends `blob-have` to all connected peers so they know where to find it.

## Local cache

The blob cache is a dedicated IndexedDB database, separate from the `"polly-state"` database used by the existing `StorageAdapter`. It must not use `StorageAdapter` — the `ChromeStorageAdapter` JSON-serializes values, which silently destroys `Uint8Array` data. The cache uses IndexedDB directly, which stores typed arrays via structured clone without serialization overhead.

```
Database: "polly-blobs" (version 1)
Object store: "blobs"
  Key: SHA-256 hex hash (string, 64 characters)
  Value: { bytes: Uint8Array, size: number, storedAt: number }
```

The cache serves three purposes:

**Performance.** A blob fetched once does not need to be fetched again. `get` and `url` check the local cache before requesting from peers.

**Offline access.** A client that goes offline can still render any blob it has previously fetched. The cache persists across sessions.

**Resume.** Partially received blobs retain their completed chunks in the cache (keyed by `blob-partial:<hash>:<index>`). Resumption picks up from the last complete chunk, not from the beginning.

Object URLs created by `url()` are cached in a `Map<string, string>` keyed by hash. Repeated calls with the same hash return the same URL. All URLs are revoked when `dispose()` is called.

The first milestone does not include cache eviction. The cache stores every blob it receives and never evicts. IndexedDB quotas on modern browsers are generous (typically 50-80% of available disk). If the quota is exceeded, the store surfaces an error. LRU eviction with pinning for referenced blobs is a future enhancement.

## Size limits

The default maximum blob size is 100 MiB, configurable per store. Blobs exceeding the limit are rejected at `put` time before any bytes are stored or transferred.

```typescript
const blobs = createBlobStore(meshAdapter, {
  maxBlobSize: 50 * 1024 * 1024, // 50 MiB
});
```

MIME type validation is not enforced by the store. The `mimeType` field in `BlobRef` is metadata supplied by the application and carried verbatim. Applications that need to restrict file types do so in their own code before calling `put`.

## Trust model

The blob store inherits the trust model of its transport.

| Property | Unencrypted blobs (`$peerState` docs) | Encrypted blobs (`$meshState` docs) |
|---|---|---|
| Server sees bytes | Never (blobs don't touch the server) | Never |
| Transfer path | Client ↔ client (WebRTC) | Client ↔ client (WebRTC) |
| Encryption | DTLS in transit | E2E (mesh key) + DTLS in transit |
| Content verification | SHA-256 on receipt | SHA-256 on decrypted plaintext |
| Availability | Requires at least one online peer with the blob | Same |

Signing applies to Automerge operations, not to blob bytes. The `BlobRef` embedded in a signed document is covered by the document's signature — a peer cannot forge a reference — but the blob bytes themselves are verified by hash. If the bytes match the hash and the hash is in a signed document, the bytes are authentic.

A `$meshState` blob encrypted with the mesh key is as private as the document itself. Compromising the key compromises both the document and its blobs. Revoking a peer's access to the document revokes its ability to decrypt new blobs. Blobs the revoked peer already downloaded and decrypted are beyond revocation — the same limitation that applies to document contents the peer has already seen.

## What the server does not do

The server stores no blob bytes. It runs no garbage collection for blobs. It serves no blob download endpoint. It has no blob-related Elysia plugin.

The server's existing responsibilities are unchanged:

- `polly()` — relay `$sharedState` messages over WebSocket
- `peerRepo()` — host Automerge-Repo for `$peerState` document sync
- `signalingServer()` — relay SDP/ICE for `$meshState` WebRTC connection setup

A `$peerState` document may contain `BlobRef` values. The server sees those values as part of the Automerge document (it holds a full replica). Server-side code — cron, HTTP handlers — can read `BlobRef` metadata (hash, filename, size, mimeType) from documents. It cannot read the blob bytes, because the bytes are not on the server. If server-side code needs to process blob contents (thumbnail generation, virus scanning, indexing), that work belongs on a dedicated cron peer with its own blob cache, participating in the mesh as an ordinary client.

## Garbage collection

Client-side garbage collection is the only kind needed. Each client scans its local Automerge documents for `BlobRef` values, builds a set of referenced hashes, and can delete any cached blob whose hash is not in the set.

The first milestone does not implement garbage collection. The cache stores everything and never deletes. At the maximum blob size of 100 MiB and realistic usage (tens to low hundreds of blobs), client-side storage is not a constraint. Automated GC is a future enhancement.

When GC is implemented, it must address a TOCTOU race: a blob can be collected between the moment `createBlobRef` returns and the moment the application embeds the `BlobRef` in a document. The mitigation is a grace period — blobs stored within the last N minutes are never collected regardless of reference state — combined with a touch-on-store mechanism that resets the grace clock when `put` is called for a blob that already exists. The sweep phase re-checks the grace timestamp before deleting. This two-phase protocol prevents the race without blocking document writes during GC.

## First milestone

1. `BlobStore` interface with `put`, `get`, `url`, `pin`, `unpin`, `size`, `evict`, `dispose` in `src/shared/lib/blob-store.ts`. No runtime imports from `tweetnacl` in this file.
2. `MemoryBlobCache` and `IndexedDBBlobCache` implementing `BlobCache` for local storage. Dedicated `"polly-blobs"` database. LRU eviction with pinning.
3. `createBlobStore(adapter, options?)` factory exported from `@fairfox/polly/mesh`.
4. Chunked transfer over the existing WebRTC data channel. Type discriminator (`"blob-chunk"`, `"blob-request"`, `"blob-have"`) in the JSON header. 64 KiB chunks. Backpressure via `bufferedAmount`.
5. Chunk-then-encrypt with per-chunk nonces. Plaintext transfer when no encryption is configured.
6. Per-operation key override via `BlobTransferOptions.key` for per-document keying.
7. `AbortSignal` support on `put` and `get`.
8. Progress callbacks for upload and download phases.
9. Multi-source fetch: re-request rotates through peers that have announced the blob, so a stalled transfer recovers against a different source.

Out of scope for this milestone: server-side blob storage, garbage collection, encrypted cache relay, TLA+ specification, `$sharedState` blob support.

## Future enhancements

These are not speculative features — each addresses a concrete limitation of the first milestone. They are deferred because the first milestone is useful without them and each can be added without breaking the API.

**Automated cache eviction policy.** The cache supports LRU eviction and pinning, but applications must call `evict(maxBytes)` themselves. A policy that evicts automatically under storage pressure (e.g. on `QuotaExceededError` or at configurable watermarks) is the natural next step.

**Parallel chunk requests across peers.** The current multi-source strategy rotates on stall — one peer at a time. A future optimisation would request different chunk ranges from multiple peers simultaneously once `total` is known, reassembling in parallel.

**Encrypted cache relay.** An optional server-side cache that holds encrypted blob ciphertext for availability when no peer is online. A separate Elysia plugin (`meshBlobCache()`), deployable alongside or independently from the signalling server. The server never holds decryption keys. TTL-based eviction.

**Multi-source parallel fetch.** Requesting different chunk ranges from different peers simultaneously. Useful in well-connected meshes with large blobs.

**Per-document encryption keys.** Blob encryption scoped to individual documents rather than the shared mesh key. Lands with the same work that brings per-document message encryption to the Automerge sync path.

**Streaming encryption.** Chunk-then-encrypt with deterministic nonce derivation to avoid holding the entire ciphertext in memory. Reduces peak memory from ~200 MiB to ~128 KiB for a 100 MiB blob. Does not change the wire protocol.

**Garbage collection.** Automated client-side GC with grace period and touch-on-store, as described in the GC section above.

## Open questions

1. **Blob availability without an encrypted cache.** If no peer with the blob is online, the blob is unavailable. For `$meshState` this is consistent with the primitive's promise (no server dependency). For `$peerState` documents with `BlobRef` values, this is a weaker availability guarantee than the document itself — the document is available from the always-on server, but the blob is not. Is this gap acceptable, or should the encrypted cache relay be promoted to milestone 1 for `$peerState` use cases?

2. **Eager vs lazy blob replication.** When a peer receives a document update containing a new `BlobRef`, should it immediately request the blob (eager — better availability, costs bandwidth and storage) or wait until the application calls `get` (lazy — economical, but the blob is unavailable offline until explicitly fetched)? The first milestone uses lazy fetch. Eager replication may be the right default for small blobs (thumbnails, avatars) and the wrong default for large ones.

3. **OPFS vs IndexedDB.** OPFS offers better performance for large files and avoids IndexedDB storage limits, but is unavailable in some browser contexts. Should the cache prefer OPFS where available and fall back to IndexedDB?

4. **Blob transfer without mesh infrastructure.** Applications using only `$peerState` that want blob support must add a signalling server and WebRTC adapter. Is there a lighter-weight blob transfer path (e.g. relaying chunks through the existing `$peerState` WebSocket) that avoids this requirement, or is requiring mesh infrastructure the right boundary?
