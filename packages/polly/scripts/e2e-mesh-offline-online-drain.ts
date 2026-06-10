#!/usr/bin/env bun
/**
 * E2e: offline → online op drain.
 *
 * Scenario: two paired peers connect through a fresh embedded relay.
 * Once both report a connected peer count, peer B is taken offline at
 * the network layer via Puppeteer's `page.setOfflineMode(true)`. Peer A
 * writes ten items to a $meshList. Peer B is brought back online.
 *
 * Success: peer B's DOM lists all ten items in the order peer A wrote
 * them, peer A's DOM still has the same ten, no silent drops fired on
 * the diagnostic stream of either peer's mesh adapter on the local
 * (server) side, and neither peer logged unexpected console output.
 *
 * This is the closest geometric analogue in polly's test surface to
 * polly#57: the unit tier's LoopbackAdapter has no disconnect
 * semantics and cannot exhibit this failure mode. Every real user
 * experiences network blips, so a regression here ships to production
 * within hours of release.
 */

export const capability = "mesh.offline-online-drain" as const;

import {
  launchPeer,
  prebakeKeyringPair,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const ITEM_COUNT = 10;
const DRAIN_TIMEOUT_MS = 20_000;

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRelay();
  const keys = prebakeKeyringPair("peer-a", "peer-b");

  const peerAServer = await serveConsumer({
    bootstrap: {
      peerId: keys.peers[0].peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: keys.peers[0].identitySecretKeyB64,
      knownPeers: {
        [keys.peers[1].peerId]: keys.peers[1].identityPublicKeyB64,
      },
      docKeyB64: keys.docKeyB64,
    },
  });
  const peerBServer = await serveConsumer({
    bootstrap: {
      peerId: keys.peers[1].peerId,
      signalingUrl: relay.url,
      identitySecretKeyB64: keys.peers[1].identitySecretKeyB64,
      knownPeers: {
        [keys.peers[0].peerId]: keys.peers[0].identityPublicKeyB64,
      },
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
    ctx.log("[e2e] both peers launched; waiting for mesh handshake");
    await waitForMeshConnected([peerA, peerB], { timeoutMs: 15_000 });

    ctx.log("[e2e] taking peer B offline");
    await peerB.page.setOfflineMode(true);

    ctx.log(`[e2e] writing ${ITEM_COUNT} items on peer A`);
    for (let i = 0; i < ITEM_COUNT; i++) {
      await peerA.page.type("[data-e2e='add-item-input']", `item-${i}`);
      await peerA.page.click("[data-e2e='add-item-button']");
    }

    // Confirm peer A's local rendering reflects all ten before bringing B back.
    await waitForConvergence([peerA], (s) => s.items.length === ITEM_COUNT, { timeoutMs: 5_000 });

    ctx.log("[e2e] bringing peer B back online; waiting for drain");
    await peerB.page.setOfflineMode(false);

    await waitForConvergence(
      [peerA, peerB],
      (s) => {
        if (s.items.length !== ITEM_COUNT) return false;
        for (let i = 0; i < ITEM_COUNT; i++) {
          if (s.items[i] !== `item-${i}`) return false;
        }
        return true;
      },
      { timeoutMs: DRAIN_TIMEOUT_MS }
    );

    ctx.log("[e2e] drain converged; running final assertions");
    await peerA.assertNoSilentDrops();
    await peerB.assertNoSilentDrops();
    peerA.assertNoUnexpectedConsole();
    peerB.assertNoUnexpectedConsole();

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    await cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
