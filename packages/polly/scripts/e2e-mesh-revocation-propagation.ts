#!/usr/bin/env bun
/**
 * E2e: revocation propagates through the RFC-043 control channel.
 *
 * Scenario: two peers, paired and synced. Peer A calls
 * `client.revokePeer(peerB.peerId, reason)` through the consumer's
 * test hook. The runtime path:
 *
 *   1. Peer A's MeshClient builds a signed RevocationRecord, applies
 *      it locally (adapter starts dropping B), and broadcasts it on
 *      the control channel with tag 0x01.
 *   2. Peer B's adapter dispatches the control-message tag, the
 *      MeshClient's onControlMessage handler decodes and verifies the
 *      record, recognises the local peer as the revocation's target,
 *      and populates `client.selfRevocation` instead of mutating the
 *      keyring.
 *   3. Peer B's diagnostic stream emits `revoke:self-targeted`; peer
 *      A's stream emits `revoke:issued`.
 *
 * The assertion set proves the protocol-level revocation works:
 *   - Peer A's selfRevocation stays undefined (it's the issuer).
 *   - Peer B's selfRevocation carries the revocation record.
 *   - Peer A's diagnostics contain `revoke:issued`.
 *   - Peer B's diagnostics contain `ctrl:revocation-received` and
 *     `revoke:self-targeted` with the issuer's peerId and the reason.
 *   - Subsequent writes from B are dropped at A with
 *     `drop:revoked-peer`, because A applied the revocation locally
 *     during step 1.
 */

export const capability = "mesh.revocation-propagation" as const;

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

    ctx.log(`[e2e] ${peerA.peerId} writes "before-revoke"`);
    await peerA.page.type("[data-e2e='add-item-input']", "before-revoke");
    await peerA.page.click("[data-e2e='add-item-button']");
    await waitForConvergence([peerA, peerB], (s) => s.items.includes("before-revoke"), {
      timeoutMs: 10_000,
    });

    ctx.log(`[e2e] ${peerA.peerId} revokes ${peerB.peerId} via the RFC-043 protocol`);
    const reason = "test scenario: revocation-propagation";
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

    // Let the broadcast travel + peer B handle the control message.
    await new Promise((r) => setTimeout(r, POST_REVOKE_SETTLE_MS));

    ctx.log("[e2e] verifying selfRevocation + diagnostic streams");
    await verifyRevocationLanded(peerA, peerB, reason);

    ctx.log("[e2e] peer B writes after revocation — peer A must drop");
    await peerB.page.type("[data-e2e='add-item-input']", "after-revoke");
    await peerB.page.click("[data-e2e='add-item-button']");
    await new Promise((r) => setTimeout(r, POST_REVOKE_SETTLE_MS));
    await verifyPeerADroppedPostRevoke(peerA, peerB.peerId);

    ctx.log("[e2e] final allow-listed assertions");
    // Peer A: revoked-peer drops are expected (it issued the revocation).
    await peerA.assertNoSilentDrops(["drop:revoked-peer"]);
    // Peer B: no silent drops at all (it is the target, not the receiver).
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

type LaunchedPeer = Awaited<ReturnType<typeof launchPeer>>;

async function readSelfRevocation(
  peer: LaunchedPeer
): Promise<{ issuerPeerId?: string; revokedPeerId?: string; reason?: string } | undefined> {
  const result = await peer.page.evaluate(() => {
    const fn = (window as unknown as { __pollyE2eSelfRevocation?: () => unknown })
      .__pollyE2eSelfRevocation;
    return fn ? fn() : undefined;
  });
  return result as { issuerPeerId?: string; revokedPeerId?: string; reason?: string } | undefined;
}

async function verifyRevocationLanded(
  peerA: LaunchedPeer,
  peerB: LaunchedPeer,
  expectedReason: string
): Promise<void> {
  const peerASelf = await readSelfRevocation(peerA);
  if (peerASelf !== undefined && peerASelf !== null) {
    throw new Error(`peer A selfRevocation should be undefined; saw ${JSON.stringify(peerASelf)}`);
  }
  const peerBSelf = await readSelfRevocation(peerB);
  if (!peerBSelf) throw new Error("peer B selfRevocation should be a record; saw undefined");
  if (peerBSelf.issuerPeerId !== peerA.peerId) {
    throw new Error(
      `peer B selfRevocation issuer is ${peerBSelf.issuerPeerId}; expected ${peerA.peerId}`
    );
  }
  if (peerBSelf.revokedPeerId !== peerB.peerId) {
    throw new Error(
      `peer B selfRevocation revokedPeerId is ${peerBSelf.revokedPeerId}; expected ${peerB.peerId}`
    );
  }
  if (peerBSelf.reason !== expectedReason) {
    throw new Error(
      `peer B selfRevocation reason is "${peerBSelf.reason}"; expected "${expectedReason}"`
    );
  }

  const peerADiags = await peerA.collectDiagnostics();
  const peerBDiags = await peerB.collectDiagnostics();
  if (!peerADiags.some((d) => d.kind === "revoke:issued")) {
    throw new Error("peer A did not emit revoke:issued");
  }
  if (!peerBDiags.some((d) => d.kind === "ctrl:revocation-received")) {
    throw new Error("peer B did not emit ctrl:revocation-received");
  }
  const peerBSelfDiag = peerBDiags.find((d) => d.kind === "revoke:self-targeted") as
    | { kind: "revoke:self-targeted"; issuerId: string; reason?: string }
    | undefined;
  if (!peerBSelfDiag) throw new Error("peer B did not emit revoke:self-targeted");
  if (peerBSelfDiag.issuerId !== peerA.peerId) {
    throw new Error(
      `peer B revoke:self-targeted issuer is ${peerBSelfDiag.issuerId}; expected ${peerA.peerId}`
    );
  }
}

async function verifyPeerADroppedPostRevoke(
  peerA: LaunchedPeer,
  peerBPeerId: string
): Promise<void> {
  const aItems = await peerA.page.evaluate(() =>
    Array.from(document.querySelectorAll("[data-e2e-item]")).map((el) => el.textContent ?? "")
  );
  if (aItems.includes("after-revoke")) {
    throw new Error(
      `peer A unexpectedly rendered "after-revoke" after revoking ${peerBPeerId}; items=${JSON.stringify(aItems)}`
    );
  }
  const peerADiags = await peerA.collectDiagnostics();
  if (!peerADiags.some((d) => d.kind === "drop:revoked-peer")) {
    throw new Error("peer A did not emit drop:revoked-peer for post-revoke writes from peer B");
  }
}

if (import.meta.main) await selfRun(capability, run);
