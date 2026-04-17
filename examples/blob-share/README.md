# blob-share — peer-to-peer file sharing with Polly

A minimal web app that demonstrates Polly's blob store and mesh WebRTC infrastructure. Two browser tabs on the same origin discover each other through a stateless signalling server, open a direct WebRTC data channel, and exchange files without the server ever touching the bytes.

## What this demonstrates

- `createBlobStore` wired to a real `MeshWebRTCAdapter`
- Encrypt-then-chunk transfer over a single shared data channel
- `blob-have` announcements when a peer joins
- `blob-request` → `blob-chunk` → reassembly → decrypt → hash-verify pipeline
- Progress callbacks, object URLs, and download via `<a>` trigger
- A stateless signalling server — the server never sees file bytes

## Run

```bash
cd examples/blob-share
bun install
bun run dev
```

Open two tabs to `http://localhost:3100`. Each tab gets its own random peer ID. Drop a file on one tab — it announces availability, and the other tab sees it appear in the list. Click "Fetch & download" to pull the bytes over WebRTC.

## What's not realistic about this demo

**The lobby uses localStorage.** Real apps discover peers out-of-band (QR pairing tokens, room URLs, invite links). This demo uses `localStorage` to let two tabs on the same origin find each other's peer IDs and public keys. This only works because they share origin — it is not how production peer discovery looks.

**The encryption key is shared via localStorage.** The mesh primitives expect keys to be provisioned through a pairing flow (see `docs/STATE.md`). This demo generates a key on first load and shares it through `localStorage` for simplicity. In real code you'd use `createPairingToken` and scan a QR.

**Everyone shares one key.** A real app would use per-document keys or a room-scoped key. Here, every tab on the same origin can decrypt everyone's files.

**No persistence between tabs closing.** The blob store uses `MemoryBlobCache` by default; pass `cache: new IndexedDBBlobCache()` in `createBlobStore(...)` to persist across sessions.

## Files

- `server/src/index.ts` — Elysia server with `signalingServer()` plugin, serves client HTML and bundles client JS on-the-fly
- `client/src/main.ts` — Full blob-share client (peer setup, UI, upload, download)
- `client/src/index.html` — Single-page UI

## How the flow works

```
Tab A                  Signalling server                Tab B
  │                          │                            │
  │ ─── WebSocket join ──► │  (Polly signalingServer)    │
  │                          │ ◄── WebSocket join ─── │
  │                          │                            │
  │ ── SDP offer (relay) ─► │ ── SDP offer (relay) ──► │
  │ ◄── SDP answer (relay) ─┤ ◄── SDP answer (relay) ──┤
  │ ── ICE candidates ─────► │ ── ICE candidates ──────► │
  │ ◄── ICE candidates ────┤ ◄── ICE candidates ────── │
  │                          │                            │
  │ ═══════════ WebRTC data channel (direct) ════════════ │
  │                                                        │
  │ ──── blob-have(hash) ───────────────────────────────►  │ (A uploads)
  │ ◄──── blob-request(hash) ─────────────────────────────  │ (B fetches)
  │ ──── blob-chunk(0/n) ──────────────────────────────► │
  │ ──── blob-chunk(1/n) ──────────────────────────────► │
  │ ──── blob-chunk(n-1/n) ────────────────────────────► │  (reassemble,
  │                                                          decrypt, verify)
```

The signalling server sees SDP and ICE bytes during handshake. After that, the WebRTC data channel carries blob traffic directly between tabs. DTLS encrypts the transport; Polly's blob store also applies application-layer encryption over the entire blob before chunking.
