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
import { createMeshClient, type MeshClient } from "../../src/shared/lib/mesh-client";
import {
  type MeshDiagnosticEvent,
  subscribeToMeshDiagnostics,
} from "../../src/shared/lib/mesh-diagnostics";
import { DEFAULT_MESH_KEY_ID, type MeshKeyring } from "../../src/shared/lib/mesh-network-adapter";
import { $meshList, configureMeshState } from "../../src/shared/lib/mesh-state";
import { signingKeyPairFromSecret } from "../../src/shared/lib/signing";

interface BootstrapSpec {
  peerId: string;
  signalingUrl: string;
  /** base64-encoded identity secret key (64 bytes) */
  identitySecretKeyB64: string;
  /** known peers as { peerId -> base64 public key } */
  knownPeers: Record<string, string>;
  /** base64-encoded document key for the default mesh key id */
  docKeyB64: string;
  /** list key to expose as a $meshList<string>; defaults to "items" */
  listKey?: string;
  /** peer ids whose writes this peer should drop at the mesh-adapter
   *  level. Pre-bakes the keyring's revokedPeers set; the test-kit uses
   *  this for revocation-shape scenarios without driving the UI flow. */
  revokedPeerIds?: string[];
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

function decodeBootstrap(spec: BootstrapSpec): {
  peerId: string;
  signalingUrl: string;
  keyring: MeshKeyring;
  listKey: string;
} {
  const identity = signingKeyPairFromSecret(fromBase64(spec.identitySecretKeyB64));
  const knownPeers = new Map<string, Uint8Array>();
  for (const [pid, b64] of Object.entries(spec.knownPeers)) {
    knownPeers.set(pid, fromBase64(b64));
  }
  const docKey = fromBase64(spec.docKeyB64);
  return {
    peerId: spec.peerId,
    signalingUrl: spec.signalingUrl,
    keyring: {
      identity,
      knownPeers,
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(spec.revokedPeerIds ?? []),
    },
    listKey: spec.listKey ?? "items",
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
  const { peerId, signalingUrl, keyring, listKey } = decodeBootstrap(spec);
  setText("[data-e2e='peer-id']", peerId);

  // Test hook: mutate the keyring's revokedPeers set at runtime. The
  // adapter re-reads the keyring on every incoming message, so the
  // revocation engages immediately.
  window.__pollyE2eRevoke = (targetPeerId: string) => {
    keyring.revokedPeers.add(targetPeerId);
    return true;
  };

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

  configureMeshState(client.repo);

  const items = $meshList<string>(listKey, []);
  await items.loaded;

  // Re-render whenever the signal changes; effect() returns a dispose fn.
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

void main();
