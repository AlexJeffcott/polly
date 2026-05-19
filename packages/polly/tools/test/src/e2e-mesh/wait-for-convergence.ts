/**
 * @fairfox/polly/test/e2e-mesh — waitForConvergence.
 *
 * Polls a consumer-supplied predicate against every launched peer until
 * the predicate returns true on all of them, or the timeout expires.
 * The predicate runs in the *node* side (the script) and is handed a
 * snapshot reader function that reads from the peer's page DOM.
 *
 * Typical use: assert every peer's `[data-e2e='items']` UL contains the
 * expected set of values.
 */

import type { LaunchedPeer } from "./launch-peer";

export interface PeerSnapshot {
  peerId: string;
  /** Items currently rendered in the consumer's [data-e2e='items'] list. */
  items: string[];
  /** Connected peer count reported by the consumer. */
  peerCount: number;
  /** Status text the consumer currently displays. */
  status: string;
}

export type ConvergencePredicate = (snapshot: PeerSnapshot) => boolean;

export interface WaitForConvergenceOptions {
  /** Cap wait time before throwing. Defaults to 20s. */
  timeoutMs?: number;
  /** Poll interval. Defaults to 200ms. */
  pollMs?: number;
}

async function readPeerSnapshot(peer: LaunchedPeer): Promise<PeerSnapshot> {
  return peer.page
    .evaluate(() => {
      const itemEls = Array.from(document.querySelectorAll("[data-e2e-item]"));
      const items = itemEls.map((el) => el.textContent ?? "");
      const peerCountText = document.querySelector("[data-e2e='peer-count']")?.textContent ?? "0";
      const status = document.querySelector("[data-e2e='status']")?.textContent ?? "";
      return { items, peerCount: Number(peerCountText) || 0, status };
    })
    .then((data) => ({ peerId: peer.peerId, ...data }));
}

/**
 * Block until the predicate is true for every peer, or throw.
 */
export async function waitForConvergence(
  peers: ReadonlyArray<LaunchedPeer>,
  predicate: ConvergencePredicate,
  options: WaitForConvergenceOptions = {}
): Promise<void> {
  const { timeoutMs = 20_000, pollMs = 200 } = options;
  const deadline = Date.now() + timeoutMs;
  let lastSnapshots: PeerSnapshot[] = [];

  while (Date.now() < deadline) {
    const snapshots = await Promise.all(peers.map(readPeerSnapshot));
    lastSnapshots = snapshots;
    if (snapshots.every(predicate)) return;
    await new Promise((r) => setTimeout(r, pollMs));
  }

  const summary = lastSnapshots
    .map(
      (s) =>
        `  ${s.peerId}: status="${s.status}" peerCount=${s.peerCount} items=${JSON.stringify(s.items)}`
    )
    .join("\n");
  throw new Error(
    `waitForConvergence: predicate did not hold for every peer within ${timeoutMs}ms.\n${summary}`
  );
}

/**
 * Convenience: wait until every peer reports it sees at least N connected
 * peers. Used right after launching to confirm the WebRTC handshake
 * completed before driving any user-facing flow.
 */
export async function waitForMeshConnected(
  peers: ReadonlyArray<LaunchedPeer>,
  options: WaitForConvergenceOptions = {}
): Promise<void> {
  const minPeers = peers.length - 1;
  await waitForConvergence(peers, (snapshot) => snapshot.peerCount >= minPeers, options);
}
