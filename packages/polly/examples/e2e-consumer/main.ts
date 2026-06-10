/**
 * @fairfox/polly e2e consumer — the smallest consumer that exercises the
 * documented mesh entry point from cold state. Driven by the test-kit.
 *
 * Boot expects a bootstrap config injected as `window.__pollyE2eBootstrap`
 * before script execution. The kit serves an HTML wrapper that sets this
 * global from JSON before importing this module. Every piece of mesh
 * state in the page goes through `createMeshClient` exactly as fairfox
 * does — this is the "documented entry point from cold state" the
 * verification policy mandates.
 *
 * Two boot modes:
 *
 *   - **Prebaked** (default): the bootstrap carries the full keyring
 *     material (`knownPeers`, `docKeyB64`) and the consumer constructs the
 *     mesh client immediately, reaching status `ready`. The drain /
 *     revocation / convergence scripts use this — they are not testing the
 *     pairing ceremony so they skip it.
 *
 *   - **Pairing** (`pairingMode: true`): the bootstrap carries only the
 *     local identity. The consumer builds an empty keyring (no known peers,
 *     no document key — exactly what a fresh device holds before scanning a
 *     token), installs the `createPairingToken` / `applyPairingToken` hooks,
 *     and reaches status `awaiting-pairing` WITHOUT constructing a mesh
 *     client. The script drives the token exchange and then calls
 *     `__pollyE2eJoinMesh()`, which constructs the client against the now-
 *     populated keyring and reaches `ready`. Deferring the join is what
 *     keeps the test honest: `createMeshClient` rejects a keyring with no
 *     document key, and joining before pairing would surface a window of
 *     `drop:unknown-peer` diagnostics that mask a real failure. The doc key
 *     travels in the token, as it does for a real first-pair.
 *
 * Surfaces exposed via `data-e2e-*` attributes:
 *   [data-e2e="status"]            — bootstrap status sentinel
 *   [data-e2e="peer-id"]           — local peerId text content
 *   [data-e2e="peer-count"]        — repo.peers.length
 *   [data-e2e="items"]             — UL containing the $meshList items
 *   [data-e2e-item]                — each LI item; text content is the value
 *   [data-e2e="add-item-input"]    — text input for a new item
 *   [data-e2e="add-item-button"]   — clicking appends to the list
 *   [data-e2e="disconnect"]        — manual disconnect button
 */

import { effect } from "@preact/signals";
import { createBlobRef } from "../../src/shared/lib/blob-ref";
import { createBlobStore } from "../../src/shared/lib/blob-store-impl";
import { generateDocumentKey } from "../../src/shared/lib/encryption";
import { createMeshClient, type MeshClient } from "../../src/shared/lib/mesh-client";
import {
  type MeshDiagnosticEvent,
  subscribeToMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";
import { DEFAULT_MESH_KEY_ID, type MeshKeyring } from "../../src/shared/lib/mesh-network-adapter";
import { $meshList, configureMeshState } from "../../src/shared/lib/mesh-state";
import {
  applyPairingToken,
  createPairingToken,
  decodePairingToken,
  encodePairingToken,
} from "../../src/shared/lib/pairing";
import { signingKeyPairFromSecret } from "../../src/shared/lib/signing";

interface BootstrapSpec {
  peerId: string;
  signalingUrl: string;
  /** base64-encoded identity secret key (64 bytes) */
  identitySecretKeyB64: string;
  /** known peers as { peerId -> base64 public key }. Omitted in pairing mode. */
  knownPeers?: Record<string, string>;
  /** base64-encoded document key for the default mesh key id. Omitted in
   *  pairing mode — the document key arrives in the pairing token. */
  docKeyB64?: string;
  /** list key to expose as a $meshList<string>; defaults to "items" */
  listKey?: string;
  /** peer ids whose writes this peer should drop at the mesh-adapter
   *  level. Pre-bakes the keyring's revokedPeers set; the test-kit uses
   *  this for revocation-shape scenarios without driving the UI flow. */
  revokedPeerIds?: string[];
  /** When true, boot into the pairing ceremony (deferred join). See the
   *  module docstring. The consumer reaches `awaiting-pairing` and waits
   *  for the script to drive `createPairingToken` / `applyPairingToken`
   *  and then `__pollyE2eJoinMesh`. */
  pairingMode?: boolean;
  /** When true, stand up a blob store (`createBlobStore`) over the mesh
   *  client's WebRTC adapter and expose the `__pollyE2eBlobPut` /
   *  `__pollyE2eBlobGet` hooks. Prebaked mode only — the blob store
   *  encrypts with the keyring's document key. */
  blobMode?: boolean;
}

declare global {
  interface Window {
    __pollyE2eBootstrap?: BootstrapSpec;
    __pollyE2eShutdown?: () => void;
    /** Live capture buffer that the test-kit reads via page.evaluate.
     *  Every mesh-diagnostics event fired in this page lands here. */
    __pollyE2eDiagnostics?: MeshDiagnosticEvent[];
    /** Test-only hook: add a peerId to the keyring's revokedPeers set
     *  at runtime. The mesh adapter re-reads the keyring on every
     *  incoming message, so the revocation takes effect on the very
     *  next message from that peer. Returns true on success, false
     *  if the bootstrap has not yet completed. */
    __pollyE2eRevoke?: (peerId: string) => boolean;
    /** Test-only hook: call the MeshClient's revokePeer through the
     *  RFC-043 protocol path — sign a RevocationRecord, apply locally,
     *  broadcast to every connected peer. */
    __pollyE2eRevokeViaProtocol?: (peerId: string, reason?: string) => Promise<boolean>;
    /** Test-only hook: read the MeshClient's selfRevocation field
     *  (the parsed record set when another peer issues a revocation
     *  naming this peer as its target). */
    __pollyE2eSelfRevocation?: () => unknown;
    /** Pairing-mode hook: act as the issuing device. Adopt a document
     *  key into the local keyring (generating one on first call) and
     *  return a base64 pairing token carrying this peer's identity
     *  public key, peer id, and the document key. */
    __pollyE2eCreatePairingToken?: () => string;
    /** Pairing-mode hook: act as the receiving device. Decode and apply
     *  a base64 pairing token, learning the issuer's public key and the
     *  shared document key. Returns true on success. */
    __pollyE2eApplyPairingToken?: (encoded: string) => boolean;
    /** Pairing-mode hook: construct the mesh client against the keyring
     *  the pairing exchange has now populated and reach `ready`. Must be
     *  called after both peers have exchanged tokens. */
    __pollyE2eJoinMesh?: () => Promise<boolean>;
    /** Blob-mode hook: store a blob (base64 bytes) through the blob store,
     *  announcing blob-have to connected peers. Returns the content hash. */
    __pollyE2eBlobPut?: (bytesB64: string, filename: string, mimeType: string) => Promise<string>;
    /** Blob-mode hook: fetch a blob by content hash, returning base64 bytes,
     *  or null while it has not yet arrived. */
    __pollyE2eBlobGet?: (hash: string) => Promise<string | null>;
  }
}

function fromBase64(b64: string): Uint8Array {
  const binary = atob(b64);
  const out = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    out[i] = binary.charCodeAt(i);
  }
  return out;
}

function toBase64(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i] as number);
  }
  return btoa(binary);
}

/** Build the full keyring from a prebaked bootstrap — the path every
 *  non-pairing script takes. */
function buildPrebakedKeyring(spec: BootstrapSpec): MeshKeyring {
  const identity = signingKeyPairFromSecret(fromBase64(spec.identitySecretKeyB64));
  const knownPeers = new Map<string, Uint8Array>();
  for (const [pid, b64] of Object.entries(spec.knownPeers ?? {})) {
    knownPeers.set(pid, fromBase64(b64));
  }
  const docKey = fromBase64(spec.docKeyB64 ?? "");
  return {
    identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(spec.revokedPeerIds ?? []),
  };
}

/** Build an empty keyring carrying only the local identity — the cold
 *  state a fresh device holds before scanning a pairing token. */
function buildPairingKeyring(spec: BootstrapSpec): MeshKeyring {
  return {
    identity: signingKeyPairFromSecret(fromBase64(spec.identitySecretKeyB64)),
    knownPeers: new Map(),
    documentKeys: new Map(),
    revokedPeers: new Set(spec.revokedPeerIds ?? []),
  };
}

function setText(selector: string, text: string): void {
  const el = document.querySelector(selector);
  if (el) el.textContent = text;
}

function renderItems(items: readonly string[]): void {
  const ul = document.querySelector("[data-e2e='items']");
  if (!ul) return;
  ul.innerHTML = "";
  for (const value of items) {
    const li = document.createElement("li");
    li.setAttribute("data-e2e-item", "");
    li.textContent = value;
    ul.appendChild(li);
  }
}

/** Install the pairing-ceremony hooks. The issuing peer adopts a document
 *  key into its own keyring before minting the token (it needs that key to
 *  encrypt its own writes); the receiving peer learns the issuer's key and
 *  the document key from the token. Both end the exchange holding each
 *  other's public keys and a shared document key. */
function installPairingHooks(keyring: MeshKeyring, peerId: string): void {
  window.__pollyE2eCreatePairingToken = (): string => {
    let docKey = keyring.documentKeys.get(DEFAULT_MESH_KEY_ID);
    if (!docKey) {
      docKey = generateDocumentKey();
      keyring.documentKeys.set(DEFAULT_MESH_KEY_ID, docKey);
    }
    const token = createPairingToken({
      identity: keyring.identity,
      issuerPeerId: peerId,
      documentKey: docKey,
      documentKeyId: DEFAULT_MESH_KEY_ID,
    });
    return encodePairingToken(token);
  };
  window.__pollyE2eApplyPairingToken = (encoded: string): boolean => {
    applyPairingToken(decodePairingToken(encoded), keyring);
    return true;
  };
}

/** Stand up a blob store over the mesh client's WebRTC adapter and install
 *  the put/get hooks. The store encrypts with the supplied document key,
 *  exactly as the blob-share example wires it. */
function installBlobHooks(client: MeshClient, key: Uint8Array): void {
  const store = createBlobStore(client.webrtcAdapter, { encrypt: { key } });
  window.__pollyE2eBlobPut = async (
    bytesB64: string,
    filename: string,
    mimeType: string
  ): Promise<string> => {
    const bytes = fromBase64(bytesB64);
    const ref = await createBlobRef({ bytes, filename, mimeType });
    await store.put(ref, bytes);
    return ref.hash;
  };
  window.__pollyE2eBlobGet = async (hash: string): Promise<string | null> => {
    const bytes = await store.get(hash);
    return bytes ? toBase64(bytes) : null;
  };
}

/** Wire the constructed mesh client into the page: $meshList rendering,
 *  peer-count display, add/disconnect controls, the client-dependent
 *  revocation hooks, and the shutdown disposer. Shared by both boot
 *  modes; the only difference between them is when it runs. */
async function activateMesh(
  client: MeshClient,
  listKey: string,
  stopDiagnostics: () => void,
  blobKey?: Uint8Array
): Promise<void> {
  configureMeshState(client.repo);

  if (blobKey) {
    installBlobHooks(client, blobKey);
  }

  window.__pollyE2eRevokeViaProtocol = async (
    targetPeerId: string,
    reason?: string
  ): Promise<boolean> => {
    await client.revokePeer(targetPeerId, reason);
    return true;
  };
  window.__pollyE2eSelfRevocation = () => client.selfRevocation;

  const items = $meshList<string>(listKey, []);
  await items.loaded;

  const stopRendering = effect(() => {
    renderItems(items.value);
  });

  const peerCountTimer = window.setInterval(() => {
    setText("[data-e2e='peer-count']", String(client.repo.peers.length));
  }, 100);

  const addInput = document.querySelector<HTMLInputElement>("[data-e2e='add-item-input']");
  const addButton = document.querySelector<HTMLButtonElement>("[data-e2e='add-item-button']");
  if (addInput && addButton) {
    addButton.addEventListener("click", () => {
      const value = addInput.value.trim();
      if (!value) return;
      items.value = [...items.value, value];
      addInput.value = "";
    });
  }

  const disconnectBtn = document.querySelector<HTMLButtonElement>("[data-e2e='disconnect']");
  disconnectBtn?.addEventListener("click", () => {
    client.disconnect();
    setText("[data-e2e='status']", "disconnected");
  });

  setText("[data-e2e='status']", "ready");

  window.__pollyE2eShutdown = () => {
    window.clearInterval(peerCountTimer);
    stopRendering();
    stopDiagnostics();
    client.disconnect();
  };
}

async function main(): Promise<void> {
  // Surface diagnostics to the test-kit. Subscribing before
  // createMeshClient means even diagnostics fired during bootstrap (e.g.
  // construction-time landmines) are captured.
  const diagnostics: MeshDiagnosticEvent[] = [];
  window.__pollyE2eDiagnostics = diagnostics;
  const stopDiagnostics = subscribeToMeshDiagnostics((event) => {
    diagnostics.push(event);
  });

  const spec = window.__pollyE2eBootstrap;
  if (!spec) {
    setText("[data-e2e='status']", "error: __pollyE2eBootstrap missing");
    stopDiagnostics();
    return;
  }

  setText("[data-e2e='status']", "booting");
  const { peerId, signalingUrl } = spec;
  const listKey = spec.listKey ?? "items";
  setText("[data-e2e='peer-id']", peerId);

  const keyring = spec.pairingMode ? buildPairingKeyring(spec) : buildPrebakedKeyring(spec);

  // Test hook: mutate the keyring's revokedPeers set at runtime. The
  // adapter re-reads the keyring on every incoming message, so the
  // revocation engages immediately. Available in both modes.
  window.__pollyE2eRevoke = (targetPeerId: string) => {
    keyring.revokedPeers.add(targetPeerId);
    return true;
  };

  if (spec.pairingMode) {
    // Deferred join: install the token hooks, reach `awaiting-pairing`,
    // and let the script drive the ceremony before any mesh client exists.
    installPairingHooks(keyring, peerId);
    window.__pollyE2eJoinMesh = async (): Promise<boolean> => {
      const client = await createMeshClient({
        signaling: { url: signalingUrl, peerId },
        keyring,
      });
      await activateMesh(client, listKey, stopDiagnostics);
      return true;
    };
    setText("[data-e2e='status']", "awaiting-pairing");
    return;
  }

  let client: MeshClient;
  try {
    client = await createMeshClient({
      signaling: { url: signalingUrl, peerId },
      keyring,
    });
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    setText("[data-e2e='status']", `bootstrap-failed: ${msg}`);
    return;
  }

  const blobKey = spec.blobMode ? keyring.documentKeys.get(DEFAULT_MESH_KEY_ID) : undefined;
  await activateMesh(client, listKey, stopDiagnostics, blobKey);
}

void main();
