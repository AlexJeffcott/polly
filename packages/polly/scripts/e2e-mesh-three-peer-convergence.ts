#!/usr/bin/env bun
/**
 * E2e: three-peer convergence.
 *
 * Scenario: three peers, all paired pairwise, all connect through a
 * fresh relay. Each peer writes one item with its own peerId as the
 * prefix. Every peer's $meshList converges on the same three items.
 *
 * This validates the kit's scaling beyond two peers and exercises a
 * three-way Automerge convergence: each peer sees its own write
 * immediately and receives the other two over the wire. The relay
 * routes signalling between each pair; WebRTC handshakes complete
 * pairwise; the mesh-network adapter encrypts and signs every message
 * over every link.
 *
 * Unlocks the runtime revocation-over-wire script that follows: that
 * test needs a B-and-C topology where A can revoke B and C must
 * concurrently observe A's revocation message.
 */

export const capability = "mesh.three-peer-convergence" as const;

import {
  knownPeersFor,
  type LaunchedPeer,
  launchPeer,
  prebakeKeyringSet,
  type ServeConsumerResult,
  serveConsumer,
  waitForConvergence,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const SETTLE_MS = 2_000;

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRelay();
  const set = prebakeKeyringSet(["peer-a", "peer-b", "peer-c"]);

  const servers: ServeConsumerResult[] = [];
  const peers: LaunchedPeer[] = [];

  const cleanup = async () => {
    for (const peer of peers) await peer.close();
    for (const server of servers) await server.close();
    await relay.close();
  };

  try {
    for (const peer of set.peers) {
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

      const launched = await launchPeer({
        peerId: peer.peerId,
        consumerUrl: server.url,
      });
      peers.push(launched);
    }

    ctx.log("[e2e] three peers launched; waiting for mesh handshake");
    await waitForMeshConnected(peers, { timeoutMs: 15_000 });

    // Settle so the WebRTC handshake has completed on every pairwise link
    // before any peer writes; otherwise an early write can race the
    // remaining link establishment and arrive before the receiver has
    // accepted the sender's identity.
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    // Writes are serialised: each peer writes one item and the script
    // waits for every peer to converge on it before the next peer
    // writes. This isolates the transport — the surface this script
    // actually tests — from $meshState's "Phase 0 naive replacement"
    // write semantics, which clobber concurrent edits and are tracked
    // for refinement under the Phase 1.1 list-splice work.
    const expected: string[] = [];
    for (const peer of peers) {
      const value = `${peer.peerId}-says-hi`;
      expected.push(value);
      ctx.log(`[e2e] ${peer.peerId} writes "${value}"`);
      await peer.page.type("[data-e2e='add-item-input']", value);
      await peer.page.click("[data-e2e='add-item-button']");
      const target = [...expected];
      await waitForConvergence(
        peers,
        (snapshot) => {
          if (snapshot.items.length !== target.length) return false;
          for (let i = 0; i < target.length; i++) {
            if (snapshot.items[i] !== target[i]) return false;
          }
          return true;
        },
        { timeoutMs: 15_000 }
      );
    }

    ctx.log("[e2e] convergence reached; running final assertions");
    for (const peer of peers) {
      await peer.assertNoSilentDrops();
      peer.assertNoUnexpectedConsole();
    }

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    await cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
