/**
 * Browser tests for MeshWebRTCAdapter in multi-peer topologies.
 *
 * Proves that the peer-discovery protocol scales beyond a pair:
 *
 *   - A three-peer mesh converges on three WebRTC connections (one per
 *     ordered pair) and documents written on any peer propagate to the
 *     other two without manual reconnection.
 *   - A bystander that joins the signalling server but is in no one's
 *     `knownPeers` does not cause any offer attempts and does not
 *     disrupt the pair that is already trusted.
 *
 * Same harness as mesh-webrtc-late-join.browser.ts — see that file for
 * the detailed comment on peer construction and the signalling URL
 * injection.
 */

import { type PeerId, Repo } from "@automerge/automerge-repo";
import { generateDocumentKey } from "../../src/shared/lib/encryption";
import {
  DEFAULT_MESH_KEY_ID,
  type MeshKeyring,
  MeshNetworkAdapter,
} from "../../src/shared/lib/mesh-network-adapter";
import { MeshSignalingClient } from "../../src/shared/lib/mesh-signaling-client";
import { MeshWebRTCAdapter } from "../../src/shared/lib/mesh-webrtc-adapter";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";
import { describe, done, expect, test, waitFor } from "../../tools/test/src/browser/harness";

const SIGNALING_URL = process.env.SIGNALING_URL ?? "ws://127.0.0.1:39000/polly/signaling";

type Doc = {
  title: string;
  count: number;
};

interface Peer {
  keyring: MeshKeyring;
  signaling: MeshSignalingClient;
  webrtc: MeshWebRTCAdapter;
  mesh: MeshNetworkAdapter;
  repo: Repo;
  peerId: string;
}

function buildPeer(peerId: string, knownPeerIds: string[], docKey: Uint8Array): Peer {
  const identity = generateSigningKeyPair();
  const keyring: MeshKeyring = {
    identity,
    knownPeers: new Map(
      knownPeerIds.map((id) => [id, new Uint8Array(32)] as [string, Uint8Array])
    ),
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
    revokedPeers: new Set(),
  };
  const webrtc = new MeshWebRTCAdapter({
    signaling: null as unknown as MeshSignalingClient,
    peerId,
    knownPeerIds,
  });
  const signaling = new MeshSignalingClient({
    url: SIGNALING_URL,
    peerId,
    onSignal: (from, payload) => webrtc.handleSignal(from, payload),
    onPeersPresent: (ids) => webrtc.handlePeersPresent(ids),
    onPeerJoined: (id) => webrtc.handlePeerJoined(id),
    onPeerLeft: (id) => webrtc.handlePeerLeft(id),
  });
  Object.assign(webrtc, { signaling });
  const mesh = new MeshNetworkAdapter({ base: webrtc, keyring });
  const repo = new Repo({ network: [mesh], peerId: peerId as unknown as PeerId });
  return { keyring, signaling, webrtc, mesh, repo, peerId };
}

async function shutdown(peer: Peer): Promise<void> {
  await peer.repo.shutdown();
  peer.signaling.close();
}

describe("MeshWebRTCAdapter in multi-peer topologies", () => {
  test("three-peer mesh: every pair connects and writes converge on all three", async () => {
    const docKey = generateDocumentKey();
    // peer-c > peer-b > peer-a under string comparison — so peer-c
    // initiates to both, peer-b initiates to peer-a.
    const a = buildPeer("peer-a", ["peer-b", "peer-c"], docKey);
    const b = buildPeer("peer-b", ["peer-a", "peer-c"], docKey);
    const c = buildPeer("peer-c", ["peer-a", "peer-b"], docKey);

    await a.signaling.connect();
    await b.signaling.connect();
    await c.signaling.connect();

    console.log("[test] waiting for each peer to reach two Automerge peers");
    await waitFor(
      () => a.repo.peers.length === 2 && b.repo.peers.length === 2 && c.repo.peers.length === 2,
      15000
    );

    // Each adapter should have exactly two slots — one for each of the
    // two other peers. No duplicates from glare.
    await new Promise((r) => setTimeout(r, 300));
    expect(a.webrtc.peerSlotCount()).toBe(2);
    expect(b.webrtc.peerSlotCount()).toBe(2);
    expect(c.webrtc.peerSlotCount()).toBe(2);

    const handleA = a.repo.create<Doc>({ title: "three-peer", count: 1 });
    await handleA.whenReady();
    const handleB = await b.repo.find<Doc>(handleA.documentId);
    const handleC = await c.repo.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "three-peer" && handleC.doc().title === "three-peer";
      } catch {
        return false;
      }
    }, 10000);

    handleC.change((d) => {
      d.count = 99;
    });
    await waitFor(() => handleA.doc().count === 99 && handleB.doc().count === 99, 10000);
    expect(handleA.doc().count).toBe(99);
    expect(handleB.doc().count).toBe(99);

    await shutdown(a);
    await shutdown(b);
    await shutdown(c);
  });

  test("stranger in the lobby: an untrusted peer does not derail trusted pairs", async () => {
    const docKey = generateDocumentKey();
    // A and B are pairwise trusted. D joins the signalling server with
    // a completely unrelated peer id and is in no one's knownPeers.
    const a = buildPeer("peer-alpha", ["peer-beta"], docKey);
    const b = buildPeer("peer-beta", ["peer-alpha"], docKey);
    const dDocKey = generateDocumentKey(); // D does not share A/B's document key either
    const d = buildPeer("peer-delta", [], dDocKey);

    await a.signaling.connect();
    await b.signaling.connect();
    await d.signaling.connect();

    await waitFor(() => a.repo.peers.length > 0 && b.repo.peers.length > 0, 10000);

    // D is joined but should never have ended up in anyone's slot map,
    // nor should D have created a slot of its own.
    await new Promise((r) => setTimeout(r, 500));
    expect(d.webrtc.peerSlotCount()).toBe(0);
    expect(a.webrtc.peerSlotCount()).toBe(1);
    expect(b.webrtc.peerSlotCount()).toBe(1);

    const handleA = a.repo.create<Doc>({ title: "no-stranger", count: 7 });
    await handleA.whenReady();
    const handleB = await b.repo.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "no-stranger";
      } catch {
        return false;
      }
    }, 10000);
    expect(handleB.doc().count).toBe(7);

    await shutdown(a);
    await shutdown(b);
    await shutdown(d);
  });
});

done();
