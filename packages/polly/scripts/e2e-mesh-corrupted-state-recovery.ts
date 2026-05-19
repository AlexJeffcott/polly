#!/usr/bin/env bun
/**
 * E2e: corrupted local state recovers from a remote peer.
 *
 * Scenario: two peers paired and synced. Peer A holds two items in
 * its `$meshList` Repo, persisted to IndexedDB. The test then wipes
 * peer A's IndexedDB databases and reloads the page. The reloaded
 * peer A boots fresh: empty Repo, empty signal value. Because the
 * keyring identity is reconstructed from the same bootstrap secret,
 * peer A re-pairs with peer B at the same peerId. Peer A's Repo
 * asks the mesh for the `items` document; peer B sends it back; the
 * signal hydrates from the network rather than from disk.
 *
 * The user-facing shape: a user clears site data, reinstalls the
 * PWA, or recovers a corrupted IDB. The mesh must repopulate the
 * doc state without losing anything; the local cache is just a
 * cache.
 *
 * Assertions:
 *   - After reload, peer A's `[data-e2e='items']` re-renders both
 *     items within the convergence window.
 *   - Peer B's diagnostic stream shows no silent drops.
 *   - Peer A's post-reload diagnostic stream shows no silent drops
 *     either — the new tab starts a fresh diagnostic buffer, so the
 *     assertion runs against the post-reload session.
 *
 * Bounds: this script does NOT corrupt an Automerge chunk byte
 * inside IDB (a sharper failure mode where the local Repo refuses
 * to load). That surface is its own test — the recovery contract
 * is different ("crash gracefully" vs "re-sync from peers"), and
 * polly's behaviour there is not yet specified.
 */

export const capability = "mesh.corrupted-state-recovery" as const;

import {
  knownPeersFor,
  launchPeer,
  prebakeKeyringSet,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";

const SETTLE_MS = 2_500;
const POST_RELOAD_SETTLE_MS = 6_000;

async function main(): Promise<void> {
  const relay = await withRelay();
  const set = prebakeKeyringSet(["peer-a", "peer-b"]);
  const peerAPeer = set.peers[0];
  const peerBPeer = set.peers[1];
  if (!peerAPeer || !peerBPeer) throw new Error("test setup: missing peer");

  const peerAServer = await serveConsumer({
    bootstrap: {
      peerId: peerAPeer.peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: peerAPeer.identitySecretKeyB64,
      knownPeers: knownPeersFor(set, peerAPeer.peerId),
      docKeyB64: set.docKeyB64,
    },
  });
  const peerBServer = await serveConsumer({
    bootstrap: {
      peerId: peerBPeer.peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: peerBPeer.identitySecretKeyB64,
      knownPeers: knownPeersFor(set, peerBPeer.peerId),
      docKeyB64: set.docKeyB64,
    },
  });

  const peerA = await launchPeer({
    peerId: peerAPeer.peerId,
    consumerUrl: peerAServer.url,
  });
  const peerB = await launchPeer({
    peerId: peerBPeer.peerId,
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
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    console.log(`[e2e] ${peerA.peerId} writes two items; waiting for convergence`);
    await peerA.page.type("[data-e2e='add-item-input']", "item-one");
    await peerA.page.click("[data-e2e='add-item-button']");
    await peerA.page.type("[data-e2e='add-item-input']", "item-two");
    await peerA.page.click("[data-e2e='add-item-button']");
    await waitForConvergence(
      [peerA, peerB],
      (s) => s.items.includes("item-one") && s.items.includes("item-two"),
      { timeoutMs: 15_000 }
    );

    console.log(`[e2e] wiping ${peerA.peerId}'s IndexedDB and reloading the page`);
    await wipeIndexedDb(peerA);
    await peerA.page.reload({ waitUntil: "domcontentloaded" });
    // Wait for the consumer to re-reach "ready" — the same precondition
    // launchPeer's initial wait used.
    await waitForStatus(peerA, "ready", 15_000);
    await new Promise((r) => setTimeout(r, POST_RELOAD_SETTLE_MS));

    console.log(
      `[e2e] verifying ${peerA.peerId} re-syncs items from ${peerB.peerId} after the wipe`
    );
    await waitForConvergence(
      [peerA],
      (s) => s.items.includes("item-one") && s.items.includes("item-two"),
      { timeoutMs: 20_000 }
    );

    console.log("[e2e] final assertions");
    // Peer B's diagnostics were captured continuously since launch.
    await peerB.assertNoSilentDrops();
    // Peer A's post-reload diagnostic buffer is fresh; assert no
    // unexpected silent drops on the reloaded session.
    await peerA.assertNoSilentDrops();
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

async function wipeIndexedDb(peer: Awaited<ReturnType<typeof launchPeer>>): Promise<void> {
  await peer.page.evaluate(async () => {
    const databases = await indexedDB.databases?.();
    if (!databases) return;
    await Promise.all(
      databases.map(
        (db) =>
          new Promise<void>((resolve, reject) => {
            if (!db.name) return resolve();
            const req = indexedDB.deleteDatabase(db.name);
            req.onsuccess = () => resolve();
            req.onerror = () => reject(req.error);
            req.onblocked = () => resolve();
          })
      )
    );
  });
}

async function waitForStatus(
  peer: Awaited<ReturnType<typeof launchPeer>>,
  expected: string,
  timeoutMs: number
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    const status = await peer.page.evaluate(
      () => document.querySelector("[data-e2e='status']")?.textContent ?? ""
    );
    if (status === expected) return;
    await new Promise((r) => setTimeout(r, 100));
  }
  throw new Error(`${peer.peerId}: status did not reach "${expected}" within ${timeoutMs}ms`);
}

await main();
