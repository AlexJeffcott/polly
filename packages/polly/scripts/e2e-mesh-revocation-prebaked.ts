#!/usr/bin/env bun
/**
 * E2e: pre-baked revocation drops the wire.
 *
 * Scenario: two peers connect through a fresh relay. Peer A's keyring
 * has peer B's id in revokedPeers from boot. Peer B types five items.
 * Peer A must:
 *   - never render those items (the adapter drops B's messages before
 *     they reach the Repo)
 *   - emit drop:revoked-peer diagnostics for each received message
 *
 * This is the second e2e surface (after offline-online-drain) and the
 * first to validate that the browser-side diagnostic stream surfaces
 * back to the test-kit. peerA.assertNoSilentDrops(["drop:revoked-peer"])
 * passes because the kind is explicitly allowed; the same call without
 * the allow list would fail loud — the gate is real, not vacuous.
 *
 * Limit of this surface: it exercises a *pre-baked* revocation. The
 * full revocation-over-wire flow (A revokes C at runtime, B observes
 * the revocation and starts dropping) is the next script.
 */

export const capability = "mesh.revocation-prebaked" as const;

import {
  launchPeer,
  prebakeKeyringPair,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";

const ITEM_COUNT = 5;
const SETTLE_MS = 4_000;

async function main(): Promise<void> {
  const relay = await withRelay();
  const keys = prebakeKeyringPair("peer-a", "peer-b");

  // Peer A pre-bakes peer-b as revoked. The keyring's knownPeers entry
  // is still present (so the diagnostic stream can report the senderId
  // verbatim) — revocation outranks knownPeers in the adapter.
  const peerAServer = await serveConsumer({
    bootstrap: {
      peerId: keys.peers[0].peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: keys.peers[0].identitySecretKeyB64,
      knownPeers: { [keys.peers[1].peerId]: keys.peers[1].identityPublicKeyB64 },
      docKeyB64: keys.docKeyB64,
      revokedPeerIds: [keys.peers[1].peerId],
    },
  });
  const peerBServer = await serveConsumer({
    bootstrap: {
      peerId: keys.peers[1].peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: keys.peers[1].identitySecretKeyB64,
      knownPeers: { [keys.peers[0].peerId]: keys.peers[0].identityPublicKeyB64 },
      docKeyB64: keys.docKeyB64,
    },
  });

  const peerA = await launchPeer({
    peerId: keys.peers[0].peerId,
    consumerUrl: peerAServer.url,
  });
  const peerB = await launchPeer({
    peerId: keys.peers[1].peerId,
    consumerUrl: peerBServer.url,
  });

  const cleanup = async () => {
    await peerA.close();
    await peerB.close();
    await peerAServer.close();
    await peerBServer.close();
    await relay.close();
  };

  try {
    console.log("[e2e] both peers launched; waiting for mesh handshake");
    await waitForMeshConnected([peerA, peerB], { timeoutMs: 15_000 });

    console.log(`[e2e] peer B writes ${ITEM_COUNT} items (peer A has B revoked)`);
    for (let i = 0; i < ITEM_COUNT; i++) {
      await peerB.page.type("[data-e2e='add-item-input']", `revoked-item-${i}`);
      await peerB.page.click("[data-e2e='add-item-button']");
    }

    // Confirm peer B's local rendering reflects all five (write succeeded locally).
    await waitForConvergence([peerB], (s) => s.items.length === ITEM_COUNT, {
      timeoutMs: 5_000,
    });

    // Give peer A a moment to receive-and-drop whatever B sent.
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    console.log("[e2e] verifying peer A stayed empty and emitted drop:revoked-peer");
    const peerASnapshot = await peerA.page.evaluate(() => ({
      items: Array.from(document.querySelectorAll("[data-e2e-item]")).map(
        (el) => el.textContent ?? ""
      ),
    }));
    if (peerASnapshot.items.length !== 0) {
      throw new Error(
        `peer A unexpectedly rendered ${peerASnapshot.items.length} items: ${JSON.stringify(peerASnapshot.items)}`
      );
    }

    const peerADiags = await peerA.collectDiagnostics();
    const revokedDrops = peerADiags.filter((d) => d.kind === "drop:revoked-peer");
    if (revokedDrops.length === 0) {
      throw new Error(
        "expected peer A to emit at least one drop:revoked-peer diagnostic; saw none"
      );
    }
    console.log(`[e2e] peer A emitted ${revokedDrops.length} drop:revoked-peer diagnostic(s)`);

    // peer A's allow-listed drop is expected; peer B should see no drops at all.
    await peerA.assertNoSilentDrops(["drop:revoked-peer"]);
    await peerB.assertNoSilentDrops();
    peerA.assertNoUnexpectedConsole();
    peerB.assertNoUnexpectedConsole();

    console.log(`[e2e] ${capability}: PASS`);
  } catch (err) {
    console.log(`[e2e] ${capability}: FAIL — ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  } finally {
    await cleanup();
  }
}

await main();
