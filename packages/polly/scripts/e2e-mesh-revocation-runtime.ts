#!/usr/bin/env bun
/**
 * E2e: runtime revocation engages on the next message.
 *
 * Scenario: two peers, paired and synced. Peer A writes "before-revoke"
 * and the script waits for two-way convergence. Peer A then revokes
 * peer B at runtime via the consumer's test hook that mutates the
 * keyring's revokedPeers set in place. The mesh adapter's
 * `keyringSource` re-reads the keyring on every incoming message
 * (`mesh-network-adapter.ts:121–119`), so the revocation engages
 * without restart on the very next message from peer B.
 *
 * Peer B then writes "after-revoke". Peer A must:
 *   - never render "after-revoke"
 *   - emit drop:revoked-peer diagnostics for B's direct messages
 *   - still render the earlier "before-revoke" item
 *
 * Two-peer geometry is deliberate. In a three-peer topology, B's
 * writes still reach A via Automerge's gossipy sync (B → C → A) even
 * when A has revoked B at the transport, because the doc-level
 * isolation needs revocation gossip — a separate flow that requires
 * a revocation-propagation protocol. This script tests only the
 * direct-link drop, which is what the adapter actually owns.
 *
 * The pre-baked equivalent script (`e2e-mesh-revocation-prebaked.ts`)
 * tests construct-time revocation. This script tests the
 * post-construction re-read contract — different surface, different
 * regression class.
 */

export const capability = "mesh.revocation-runtime-direct" as const;

import {
  knownPeersFor,
  launchPeer,
  prebakeKeyringSet,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const SETTLE_MS = 2_000;
const POST_REVOKE_SETTLE_MS = 4_000;

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRelay();
  const set = prebakeKeyringSet(["peer-a", "peer-b"]);

  const peerAPeer = set.peers[0];
  const peerBPeer = set.peers[1];
  if (!peerAPeer || !peerBPeer) throw new Error("test setup: prebakeKeyringSet returned <2 peers");

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
    ctx.log("[e2e] both peers launched; waiting for mesh handshake");
    await waitForMeshConnected([peerA, peerB], { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    ctx.log(`[e2e] ${peerA.peerId} writes "before-revoke"; waiting for convergence`);
    await peerA.page.type("[data-e2e='add-item-input']", "before-revoke");
    await peerA.page.click("[data-e2e='add-item-button']");
    await waitForConvergence([peerA, peerB], (s) => s.items.includes("before-revoke"), {
      timeoutMs: 10_000,
    });

    ctx.log(`[e2e] ${peerA.peerId} revokes ${peerB.peerId} at runtime`);
    const revoked = await peerA.page.evaluate((targetPeerId: string) => {
      const fn = (window as unknown as { __pollyE2eRevoke?: (id: string) => boolean })
        .__pollyE2eRevoke;
      return fn ? fn(targetPeerId) : false;
    }, peerB.peerId);
    if (!revoked) throw new Error("peer A revocation hook missing");

    ctx.log(`[e2e] ${peerB.peerId} writes "after-revoke"`);
    await peerB.page.type("[data-e2e='add-item-input']", "after-revoke");
    await peerB.page.click("[data-e2e='add-item-button']");

    // Peer B's own rendering must reflect its write locally (the write
    // succeeded; the drop happens at peer A's adapter, not at B's).
    await waitForConvergence([peerB], (s) => s.items.includes("after-revoke"), {
      timeoutMs: 10_000,
    });

    // Give peer A's adapter time to receive-and-drop.
    await new Promise((r) => setTimeout(r, POST_REVOKE_SETTLE_MS));

    ctx.log("[e2e] verifying peer A dropped the post-revoke write");
    const aItems = await peerA.page.evaluate(() =>
      Array.from(document.querySelectorAll("[data-e2e-item]")).map((el) => el.textContent ?? "")
    );
    if (aItems.includes("after-revoke")) {
      throw new Error(
        `peer A unexpectedly rendered "after-revoke" after revoking ${peerB.peerId}; items=${JSON.stringify(aItems)}`
      );
    }
    if (!aItems.includes("before-revoke")) {
      throw new Error(
        `peer A lost "before-revoke" after revoking ${peerB.peerId}; items=${JSON.stringify(aItems)}`
      );
    }

    const peerADiags = await peerA.collectDiagnostics();
    const revokedDrops = peerADiags.filter((d) => d.kind === "drop:revoked-peer");
    if (revokedDrops.length === 0) {
      throw new Error(
        "expected peer A to emit at least one drop:revoked-peer diagnostic after revoking peer B; saw none"
      );
    }
    ctx.log(`[e2e] peer A emitted ${revokedDrops.length} drop:revoked-peer diagnostic(s)`);

    await peerA.assertNoSilentDrops(["drop:revoked-peer"]);
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
