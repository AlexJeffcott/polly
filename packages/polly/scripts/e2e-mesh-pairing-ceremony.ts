#!/usr/bin/env bun
/**
 * E2e: pairing ceremony from cold state.
 *
 * Every other mesh e2e *prebakes* the keyring — both peers boot already
 * knowing each other's public keys and sharing a document key. That skips
 * the one surface a real first-time user cannot skip: the pairing
 * ceremony, where two devices that know nothing about each other exchange
 * identity keys and a document key over an out-of-band channel (a QR code,
 * a copy-pasted link) before any sync can happen. A factory gap in that
 * path would be invisible to all seven prebaked scripts — exactly the
 * polly#57 failure shape, where every test hand-wired around the seam the
 * real user actually crosses.
 *
 * This script drives the documented `createPairingToken` /
 * `applyPairingToken` flow (`@fairfox/polly/mesh`) end to end:
 *
 *   1. Two peers boot cold. Each holds ONLY its own identity — no known
 *      peers, no document key. Neither constructs a mesh client yet
 *      (`createMeshClient` rejects a keyring with no document key, and a
 *      premature join would emit `drop:unknown-peer` noise). They reach
 *      `awaiting-pairing` and wait.
 *   2. Peer A acts as issuer: mints a pairing token carrying its public
 *      key, peer id, and a freshly-generated document key. The token is a
 *      ~200-byte base64 string — the thing a real app renders as a QR code.
 *   3. The script carries A's token to B out of band (here: node-side
 *      string passing, standing in for the QR scan) and B applies it,
 *      learning A's key and the document key.
 *   4. Pairing is one-way per token, so B mints its own token (reusing the
 *      document key it just adopted) and A applies it. Now both peers hold
 *      each other's public keys and a shared document key — the same end
 *      state the prebaked path hands the other scripts for free.
 *   5. Both peers join the mesh. The WebRTC handshake completes, A and B
 *      each write an item, and the script asserts BIDIRECTIONAL
 *      convergence: A sees B's write and B sees A's write. Bidirectional
 *      is the point — the adapter drops messages from any peer absent from
 *      `knownPeers`, so convergence in both directions can only happen if
 *      both tokens were applied correctly.
 *
 * The primary assertion is convergence; `assertNoSilentDrops` then runs
 * clean (no allow-list) because the deferred join means no message ever
 * crossed the wire before both keyrings were complete.
 */

export const capability = "mesh.pairing-ceremony" as const;

import {
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

/** Read the issuer's freshly-minted pairing token out of the page. */
async function createToken(peer: LaunchedPeer): Promise<string> {
  const token = await peer.page.evaluate(() => {
    const fn = (window as unknown as { __pollyE2eCreatePairingToken?: () => string })
      .__pollyE2eCreatePairingToken;
    if (!fn) throw new Error("__pollyE2eCreatePairingToken hook missing");
    return fn();
  });
  if (!token) throw new Error(`createToken(${peer.peerId}): empty token`);
  return token;
}

/** Apply a token to the receiving peer's keyring. */
async function applyToken(peer: LaunchedPeer, token: string): Promise<void> {
  const ok = await peer.page.evaluate((encoded) => {
    const fn = (window as unknown as { __pollyE2eApplyPairingToken?: (e: string) => boolean })
      .__pollyE2eApplyPairingToken;
    if (!fn) throw new Error("__pollyE2eApplyPairingToken hook missing");
    return fn(encoded);
  }, token);
  if (!ok) throw new Error(`applyToken(${peer.peerId}): hook returned false`);
}

/** Construct the deferred mesh client now the keyring is complete. */
async function joinMesh(peer: LaunchedPeer): Promise<void> {
  const ok = await peer.page.evaluate(async () => {
    const fn = (window as unknown as { __pollyE2eJoinMesh?: () => Promise<boolean> })
      .__pollyE2eJoinMesh;
    if (!fn) throw new Error("__pollyE2eJoinMesh hook missing");
    return fn();
  });
  if (!ok) throw new Error(`joinMesh(${peer.peerId}): hook returned false`);
  // The join flips the consumer to "ready"; wait for it so a subsequent
  // write does not race the $meshList wiring.
  const deadline = Date.now() + 15_000;
  while (Date.now() < deadline) {
    const status = await peer.page.evaluate(
      () => document.querySelector("[data-e2e='status']")?.textContent ?? ""
    );
    if (status === "ready") return;
    await new Promise((r) => setTimeout(r, 100));
  }
  throw new Error(`joinMesh(${peer.peerId}): consumer did not reach "ready" after join`);
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRelay();
  // We only use prebakeKeyringSet for its identity keypairs; the shared
  // document key it generates is deliberately ignored — the whole point is
  // that the document key reaches the receiver through the pairing token,
  // not through the bootstrap.
  const set = prebakeKeyringSet(["peer-a", "peer-b"]);

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
          pairingMode: true,
        },
      });
      servers.push(server);

      const launched = await launchPeer({
        peerId: peer.peerId,
        consumerUrl: server.url,
        readyStatus: "awaiting-pairing",
      });
      peers.push(launched);
    }

    const [peerA, peerB] = peers as [LaunchedPeer, LaunchedPeer];
    ctx.log("[e2e] both peers cold (awaiting-pairing); driving the token exchange");

    // A issues, B receives — B now knows A and holds the document key.
    const tokenA = await createToken(peerA);
    await applyToken(peerB, tokenA);
    ctx.log("[e2e] peer B applied peer A's token");

    // B issues (reusing the adopted document key), A receives — A now
    // knows B. Both keyrings are complete.
    const tokenB = await createToken(peerB);
    if (process.env["FALSIFY_SKIP_REVERSE_PAIR"] !== "1") {
      await applyToken(peerA, tokenB);
    }
    ctx.log("[e2e] peer A applied peer B's token; keyrings complete");

    // Join the mesh now both peers hold each other's keys and a shared
    // document key. Deferring to here is what keeps assertNoSilentDrops
    // clean.
    await joinMesh(peerA);
    await joinMesh(peerB);
    ctx.log("[e2e] both peers joined the mesh; waiting for handshake");

    await waitForMeshConnected(peers, { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    // Bidirectional convergence: each peer writes one item, and every peer
    // must converge on the full set. A reverse-direction failure (A never
    // learns B's key) shows up here as a timeout, not a silent pass.
    const expected: string[] = [];
    for (const peer of peers) {
      const value = `${peer.peerId}-paired-write`;
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

    ctx.log("[e2e] bidirectional convergence reached; running final assertions");
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
