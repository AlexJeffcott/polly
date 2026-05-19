#!/usr/bin/env bun
/**
 * E2e: revocation propagates to peers that join after issue-time.
 *
 * Scenario: peers A and B launch and pair. Peer A revokes peer B
 * through the RFC-043 protocol path. Peer C — who was not connected
 * at any point during the revocation — launches and joins the mesh.
 * The peer-candidate hook on both A and C exchanges revocation-set
 * summaries; peer A's summary lists B's revocation while peer C's is
 * empty; peer A pushes the full encoded record to peer C through tag
 * 0x01; peer C applies it.
 *
 * This shape (launch a peer after the revocation) is the honest
 * version of the "offline at issue-time" case. Puppeteer's
 * setOfflineMode does not actually sever an established WebRTC data
 * channel — the existing channel keeps carrying traffic — so a peer
 * that was online when the revocation broadcast went out would
 * receive it through the still-open channel even though setOffline
 * was meant to simulate a network drop. Launching a fresh peer is
 * the cleanest way to guarantee it has no path to the revocation
 * until the summary exchange on connect.
 *
 * Assertions:
 *   - Peer C's diagnostic stream contains
 *     `ctrl:revocation-summary-received`, `ctrl:revocation-received`,
 *     and `revoke:applied` (proves the catch-up push landed).
 *   - Peer C's adapter drops a subsequent write from peer B with
 *     `drop:revoked-peer`, confirming the revocation engaged.
 */

export const capability = "mesh.revocation-offline-catchup" as const;

import {
  knownPeersFor,
  type LaunchedPeer,
  launchPeer,
  type PrebakedPeer,
  prebakeKeyringSet,
  type ServeConsumerResult,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";

const SETTLE_MS = 2_000;
const POST_REVOKE_SETTLE_MS = 4_000;
const POST_RECONNECT_SETTLE_MS = 6_000;

async function main(): Promise<void> {
  const relay = await withRelay();
  const set = prebakeKeyringSet(["peer-a", "peer-b", "peer-c"]);
  const peerAPeer = set.peers[0];
  const peerBPeer = set.peers[1];
  const peerCPeer = set.peers[2];
  if (!peerAPeer || !peerBPeer || !peerCPeer) throw new Error("test setup: missing peer");

  const servers: ServeConsumerResult[] = [];
  const launched: LaunchedPeer[] = [];

  const cleanup = async () => {
    for (const peer of launched) await peer.close();
    for (const server of servers) await server.close();
    await relay.close();
  };

  async function launchOne(peer: PrebakedPeer): Promise<LaunchedPeer> {
    const server = await serveConsumer({
      bootstrap: {
        peerId: peer.peerId,
        signalingUrl: relay.url,
        identitySecretKeyB64: peer.identitySecretKeyB64,
        knownPeers: knownPeersFor(set, peer.peerId),
        docKeyB64: set.docKeyB64,
      },
    });
    servers.push(server);
    const handle = await launchPeer({
      peerId: peer.peerId,
      consumerUrl: server.url,
    });
    launched.push(handle);
    return handle;
  }

  try {
    console.log("[e2e] launching peer A and peer B; peer C stays offline");
    const peerA = await launchOne(peerAPeer);
    const peerB = await launchOne(peerBPeer);
    await waitForMeshConnected([peerA, peerB], { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    console.log(`[e2e] ${peerA.peerId} writes "before-revoke"; waiting for A↔B convergence`);
    await peerA.page.type("[data-e2e='add-item-input']", "before-revoke");
    await peerA.page.click("[data-e2e='add-item-button']");
    await waitForConvergence([peerA, peerB], (s) => s.items.includes("before-revoke"), {
      timeoutMs: 10_000,
    });

    console.log(
      `[e2e] ${peerA.peerId} revokes ${peerB.peerId} while ${peerCPeer.peerId} is not yet launched`
    );
    const reason = "test scenario: offline catchup";
    const ok = await peerA.page.evaluate(
      async (args: { peerId: string; reason: string }) => {
        const fn = (
          window as unknown as {
            __pollyE2eRevokeViaProtocol?: (id: string, reason?: string) => Promise<boolean>;
          }
        ).__pollyE2eRevokeViaProtocol;
        if (!fn) return false;
        return fn(args.peerId, args.reason);
      },
      { peerId: peerB.peerId, reason }
    );
    if (!ok) throw new Error("peer A revokeViaProtocol hook missing");
    await new Promise((r) => setTimeout(r, POST_REVOKE_SETTLE_MS));

    console.log(`[e2e] launching ${peerCPeer.peerId}; awaiting summary exchange`);
    const peerC = await launchOne(peerCPeer);
    await waitForMeshConnected([peerA, peerB, peerC], { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, POST_RECONNECT_SETTLE_MS));

    await verifyCatchUpOnC(peerC, peerB.peerId);
    await verifyDropAfterCatchUp(peerB, peerC);

    console.log("[e2e] final allow-listed assertions");
    await peerA.assertNoSilentDrops(["drop:revoked-peer"]);
    await peerB.assertNoSilentDrops();
    await peerC.assertNoSilentDrops(["drop:revoked-peer"]);
    for (const peer of [peerA, peerB, peerC]) peer.assertNoUnexpectedConsole();

    console.log(`[e2e] ${capability}: PASS`);
  } catch (err) {
    console.log(`[e2e] ${capability}: FAIL — ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  } finally {
    await cleanup();
  }
}

async function verifyCatchUpOnC(peerC: LaunchedPeer, expectedRevokedPeerId: string): Promise<void> {
  const diags = await peerC.collectDiagnostics();
  if (!diags.some((d) => d.kind === "ctrl:revocation-summary-received")) {
    throw new Error("peer C did not receive a revocation-summary on connect");
  }
  if (!diags.some((d) => d.kind === "ctrl:revocation-received")) {
    throw new Error("peer C did not receive the catch-up revocation blob pushed by peer A");
  }
  const applied = diags.find((d) => d.kind === "revoke:applied") as
    | { kind: "revoke:applied"; revokedPeerId: string }
    | undefined;
  if (!applied) throw new Error("peer C did not apply any catch-up revocation");
  if (applied.revokedPeerId !== expectedRevokedPeerId) {
    throw new Error(
      `peer C applied a revocation targeting ${applied.revokedPeerId}; expected ${expectedRevokedPeerId}`
    );
  }
}

async function verifyDropAfterCatchUp(peerB: LaunchedPeer, peerC: LaunchedPeer): Promise<void> {
  console.log(`[e2e] ${peerB.peerId} writes "after-revoke" — peer C must drop`);
  await peerB.page.type("[data-e2e='add-item-input']", "after-revoke");
  await peerB.page.click("[data-e2e='add-item-button']");
  await new Promise((r) => setTimeout(r, 4_000));

  const items = await peerC.page.evaluate(() =>
    Array.from(document.querySelectorAll("[data-e2e-item]")).map((el) => el.textContent ?? "")
  );
  if (items.includes("after-revoke")) {
    throw new Error(
      `peer C unexpectedly rendered "after-revoke" after applying the revocation; items=${JSON.stringify(items)}`
    );
  }
  const diags = await peerC.collectDiagnostics();
  if (!diags.some((d) => d.kind === "drop:revoked-peer")) {
    throw new Error("peer C did not emit drop:revoked-peer for post-revoke writes from peer B");
  }
}

await main();
