/**
 * blob-share client
 *
 * A minimal web app that demonstrates Polly's peer-to-peer blob store.
 * Two browser tabs (or devices) connect through a stateless signalling
 * server, then exchange files directly over WebRTC data channels. The
 * server never sees file bytes.
 *
 * Flow:
 * 1. Generate an ephemeral peer ID and signing keypair
 * 2. Register with the shared "lobby" — every peer knows every other peer
 * 3. Open WebRTC connections via Polly's MeshWebRTCAdapter
 * 4. Create a blob store piggybacking on that adapter
 * 5. Drop a file → store.put() → announce blob-have to connected peers
 * 6. Receiver sees the announcement, fetches, and displays
 */

import {
  createBlobRef,
  createBlobStore,
  generateDocumentKey,
  generateSigningKeyPair,
  MeshSignalingClient,
  MeshWebRTCAdapter,
} from "@fairfox/polly/mesh";

// ---------------------------------------------------------------------------
// Known-peer lobby
// ---------------------------------------------------------------------------
//
// The signalling server is a relay — it doesn't do peer discovery. For a
// real app, you'd use a room protocol or an out-of-band introduction.
// For a demo, we use localStorage as a shared "lobby" so tabs can find
// each other. This is not how production code looks — it's a demo shortcut
// that works because both tabs share origin.

const LOBBY_KEY = "polly-blob-share:lobby";

interface LobbyEntry {
  peerId: string;
  publicKey: string; // hex-encoded
  timestamp: number;
}

function readLobby(): LobbyEntry[] {
  try {
    const raw = localStorage.getItem(LOBBY_KEY);
    if (!raw) return [];
    const entries = JSON.parse(raw) as LobbyEntry[];
    // Drop entries older than 30s.
    const now = Date.now();
    return entries.filter((e) => now - e.timestamp < 30_000);
  } catch {
    return [];
  }
}

function writeLobby(entries: LobbyEntry[]): void {
  localStorage.setItem(LOBBY_KEY, JSON.stringify(entries));
}

function announceToLobby(entry: LobbyEntry): void {
  const entries = readLobby().filter((e) => e.peerId !== entry.peerId);
  entries.push(entry);
  writeLobby(entries);
}

function removeFromLobby(peerId: string): void {
  writeLobby(readLobby().filter((e) => e.peerId !== peerId));
}

// ---------------------------------------------------------------------------
// Demo encryption key
// ---------------------------------------------------------------------------
//
// In a real app this key would come from a pairing token (see
// docs/STATE.md). For this demo, every tab in the same browser shares a
// single key through localStorage. Fine for the demo, awful for real use.

const SHARED_KEY = "polly-blob-share:docKey";

function getOrCreateSharedKey(): Uint8Array {
  const stored = localStorage.getItem(SHARED_KEY);
  if (stored) {
    return new Uint8Array(stored.split(",").map((n) => Number.parseInt(n, 10)));
  }
  const key = generateDocumentKey();
  localStorage.setItem(SHARED_KEY, Array.from(key).join(","));
  return key;
}

// ---------------------------------------------------------------------------
// UI helpers
// ---------------------------------------------------------------------------

const $ = <T extends HTMLElement>(id: string): T => {
  const el = document.getElementById(id);
  if (!el) throw new Error(`#${id} not found`);
  return el as T;
};

function log(message: string, level: "info" | "error" = "info"): void {
  const line = document.createElement("div");
  line.className = `log-line ${level === "error" ? "error" : ""}`;
  const time = new Date().toLocaleTimeString();
  line.textContent = `[${time}] ${message}`;
  $("log").appendChild(line);
  $("log").scrollTop = $("log").scrollHeight;
}

function formatBytes(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KiB`;
  return `${(bytes / 1024 / 1024).toFixed(1)} MiB`;
}

function toHex(bytes: Uint8Array): string {
  return Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, "0"))
    .join("");
}

function fromHex(hex: string): Uint8Array {
  const result = new Uint8Array(hex.length / 2);
  for (let i = 0; i < result.length; i++) {
    result[i] = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return result;
}

// ---------------------------------------------------------------------------
// File list state
// ---------------------------------------------------------------------------

interface FileEntry {
  hash: string;
  filename: string;
  mimeType: string;
  size: number;
  status: "local" | "remote" | "downloading";
  progress: number; // 0..1
}

const files = new Map<string, FileEntry>();
let downloadHandler: (entry: FileEntry) => void = () => {
  /* set by main() once the store is ready */
};

function renderFiles(): void {
  const list = $("file-list");
  list.innerHTML = "";

  if (files.size === 0) {
    list.innerHTML =
      '<div style="color: #64748b; text-align: center; padding: 2rem;">No files shared yet</div>';
    return;
  }

  for (const entry of files.values()) {
    const item = document.createElement("div");
    item.className = "file-item";

    const info = document.createElement("div");
    info.className = "file-info";
    const name = document.createElement("div");
    name.className = "file-name";
    name.textContent = entry.filename;
    const meta = document.createElement("div");
    meta.className = "file-meta";
    meta.textContent = `${formatBytes(entry.size)} · ${entry.mimeType || "application/octet-stream"} · ${entry.hash.slice(0, 12)}…`;
    info.appendChild(name);
    info.appendChild(meta);

    if (entry.status === "downloading") {
      const progress = document.createElement("div");
      progress.className = "progress";
      const bar = document.createElement("div");
      bar.className = "progress-bar";
      bar.style.width = `${Math.round(entry.progress * 100)}%`;
      progress.appendChild(bar);
      info.appendChild(progress);
    }

    const status = document.createElement("div");
    status.className = `file-status status-${entry.status}`;
    status.textContent =
      entry.status === "local" ? "local" : entry.status === "remote" ? "available" : "downloading…";

    const actions = document.createElement("div");
    actions.className = "file-actions";
    if (entry.status !== "downloading") {
      const btn = document.createElement("button");
      btn.textContent = entry.status === "local" ? "Download" : "Fetch & download";
      btn.addEventListener("click", () => downloadHandler(entry));
      actions.appendChild(btn);
    }

    item.appendChild(info);
    item.appendChild(status);
    item.appendChild(actions);
    list.appendChild(item);
  }
}

// ---------------------------------------------------------------------------
// Bootstrap
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
  const identity = generateSigningKeyPair();
  const myPeerId = `peer-${Math.random().toString(36).slice(2, 10)}`;
  const docKey = getOrCreateSharedKey();

  $("peer-id").textContent = myPeerId;
  log(`bootstrapping as ${myPeerId}`);

  // Read the lobby to find other peers.
  const otherPeers = readLobby();
  log(`found ${otherPeers.length} peer(s) in lobby`);

  // Announce ourselves.
  announceToLobby({
    peerId: myPeerId,
    publicKey: toHex(identity.publicKey),
    timestamp: Date.now(),
  });

  // Refresh our announcement every 10s so we don't get aged out.
  setInterval(() => {
    announceToLobby({
      peerId: myPeerId,
      publicKey: toHex(identity.publicKey),
      timestamp: Date.now(),
    });
  }, 10_000);

  window.addEventListener("beforeunload", () => {
    removeFromLobby(myPeerId);
  });

  // Build keyring.
  const knownPeers = new Map<string, Uint8Array>();
  for (const entry of otherPeers) {
    knownPeers.set(entry.peerId, fromHex(entry.publicKey));
  }

  // Create adapters.
  const webrtc = new MeshWebRTCAdapter({
    signaling: null as unknown as MeshSignalingClient,
    peerId: myPeerId,
    knownPeerIds: otherPeers.map((p) => p.peerId),
  });
  const signaling = new MeshSignalingClient({
    // nosemgrep: javascript.lang.security.detect-insecure-websocket.detect-insecure-websocket — local-dev example; production deployments swap to wss://.
    url: `ws://${window.location.host}/polly/signaling`,
    peerId: myPeerId,
    onSignal: (from, payload) => webrtc.handleSignal(from, payload),
  });
  Object.assign(webrtc, { signaling });

  signaling
    .connect()
    .then(() => {
      const status = $("signaling-status");
      status.textContent = "connected";
      status.classList.remove("disconnected");
      status.classList.add("connected");
      log("signalling connected");
    })
    .catch((err) => {
      log(`signalling failed: ${err}`, "error");
    });

  // Create the blob store. Encrypt-then-chunk with the shared demo key.
  const blobs = createBlobStore(webrtc, { encrypt: { key: docKey } });

  // Watch for peer connections. We use the Automerge NetworkAdapter events.
  let peerCount = 0;
  webrtc.on("peer-candidate", (event: { peerId: unknown }) => {
    peerCount++;
    $("peer-count").textContent = String(peerCount);
    log(`peer connected: ${String(event.peerId)}`);
  });
  webrtc.on("peer-disconnected", (event: { peerId: unknown }) => {
    peerCount = Math.max(0, peerCount - 1);
    $("peer-count").textContent = String(peerCount);
    log(`peer disconnected: ${String(event.peerId)}`);
  });

  // Intercept blob-have announcements so we can surface remote blobs in
  // the UI before the user asks for them. The blob store's own
  // onBlobMessage handler is already set — we wrap it to add our UI hook.
  const originalHandler = webrtc.onBlobMessage;
  webrtc.onBlobMessage = (peerId, header, data) => {
    originalHandler?.(peerId, header, data);
    if (header["type"] === "blob-have") {
      const hash = header["hash"] as string;
      if (!files.has(hash)) {
        // We know this hash exists on another peer but we don't know
        // filename/mime/size until we fetch. Create a stub entry.
        files.set(hash, {
          hash,
          filename: `${hash.slice(0, 8)}.bin`,
          mimeType: "application/octet-stream",
          size: 0,
          status: "remote",
          progress: 0,
        });
        log(`announcement: peer has ${hash.slice(0, 12)}…`);
        renderFiles();
      }
    }
  };

  // ---- File upload via drop zone ----
  const dropZone = $("drop-zone");
  const fileInput = $<HTMLInputElement>("file-input");

  fileInput.addEventListener("change", async () => {
    if (fileInput.files) {
      for (const file of Array.from(fileInput.files)) {
        await uploadFile(file);
      }
    }
    fileInput.value = "";
  });

  dropZone.addEventListener("dragover", (e) => {
    e.preventDefault();
    dropZone.classList.add("drag-over");
  });
  dropZone.addEventListener("dragleave", () => {
    dropZone.classList.remove("drag-over");
  });
  dropZone.addEventListener("drop", async (e) => {
    e.preventDefault();
    dropZone.classList.remove("drag-over");
    if (e.dataTransfer?.files) {
      for (const file of Array.from(e.dataTransfer.files)) {
        await uploadFile(file);
      }
    }
  });

  async function uploadFile(file: File): Promise<void> {
    log(`uploading ${file.name} (${formatBytes(file.size)})`);
    const bytes = new Uint8Array(await file.arrayBuffer());
    const ref = await createBlobRef({
      bytes,
      filename: file.name,
      mimeType: file.type || "application/octet-stream",
    });

    files.set(ref.hash, {
      hash: ref.hash,
      filename: ref.filename,
      mimeType: ref.mimeType,
      size: ref.size,
      status: "local",
      progress: 1,
    });
    renderFiles();

    await blobs.put(ref, bytes, {
      onProgress: (event) => {
        if (event.phase === "encrypting" && event.total) {
          log(`encrypting ${file.name}: ${Math.round((event.loaded / event.total) * 100)}%`);
        }
      },
    });
    log(`uploaded ${file.name} and announced to peers`);
  }

  downloadHandler = async (entry: FileEntry): Promise<void> => {
    if (entry.status === "local") {
      // Already have bytes locally — create a blob URL for download.
      const url = await blobs.url(entry.hash);
      if (url) triggerDownload(url, entry.filename);
      return;
    }

    entry.status = "downloading";
    entry.progress = 0;
    renderFiles();

    try {
      log(`fetching ${entry.hash.slice(0, 12)}…`);
      const received = await blobs.get(entry.hash, {
        onProgress: (event) => {
          if (event.phase === "downloading") {
            // We don't know total until all chunks arrive; use loaded as
            // a rough indicator that progress is happening.
            entry.progress = Math.min(0.95, entry.progress + 0.1);
            renderFiles();
          } else if (event.phase === "decrypting" && event.total) {
            entry.progress = 0.98;
            renderFiles();
          }
        },
      });

      if (!received) {
        entry.status = "remote";
        entry.progress = 0;
        renderFiles();
        log(`fetch failed: no peer returned ${entry.hash.slice(0, 12)}`, "error");
        return;
      }

      entry.size = received.length;
      entry.status = "local";
      entry.progress = 1;
      renderFiles();
      log(`received ${formatBytes(received.length)} (${entry.hash.slice(0, 12)}…)`);

      const url = await blobs.url(entry.hash);
      if (url) triggerDownload(url, entry.filename);
    } catch (err) {
      entry.status = "remote";
      entry.progress = 0;
      renderFiles();
      log(`fetch failed: ${err instanceof Error ? err.message : String(err)}`, "error");
    }
  };

  function triggerDownload(url: string, filename: string): void {
    const a = document.createElement("a");
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
  }

  renderFiles();
}

main().catch((err) => {
  log(`fatal: ${err instanceof Error ? err.message : String(err)}`, "error");
});
