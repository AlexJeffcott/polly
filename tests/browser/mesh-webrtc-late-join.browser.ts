/**
 * Browser tests for MeshWebRTCAdapter's peer-discovery across realistic
 * join orderings. The aim is to prove that two devices with mutual
 * trust converge on their documents whenever they are joined to the
 * same signalling server at any overlapping moment — regardless of who
 * joined first and whether one side was already stalled on an earlier
 * attempt.
 *
 * All four scenarios stage two full stacks (keyring, signalling client,
 * webrtc adapter, network adapter, Repo) in one Puppeteer tab,
 * sequence their `signalingClient.connect()` calls, and assert that the
 * documents round-trip through real WebRTC data channels.
 *
 * The signalling server is the reference Elysia plugin started by
 * tools/test/src/browser/run.ts on an ephemeral port; the URL is
 * injected into the bundle via process.env.SIGNALING_URL.
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
  identity: ReturnType<typeof generateSigningKeyPair>;
  keyring: MeshKeyring;
  signaling: MeshSignalingClient;
  webrtc: MeshWebRTCAdapter;
  mesh: MeshNetworkAdapter;
  repo: Repo;
  peerId: string;
}

type Identities = Map<string, ReturnType<typeof generateSigningKeyPair>>;

function preGenerateIdentities(peerIds: string[]): Identities {
  const identities: Identities = new Map();
  for (const id of peerIds) identities.set(id, generateSigningKeyPair());
  return identities;
}

// Build one peer's full stack. Keyring carries real public keys for
// every peer in `knownPeerIds`, so MeshNetworkAdapter's signature
// verification passes when bytes flow. Signalling-client wires the
// three discovery callbacks into the adapter's dispatch methods.
// Does not call signaling.connect(); the test orders those calls.
function buildPeer(
  peerId: string,
  knownPeerIds: string[],
  docKey: Uint8Array,
  identities: Identities
): Peer {
  const identity = identities.get(peerId);
  if (!identity) throw new Error(`missing identity for ${peerId}`);
  const knownPeers = new Map<string, Uint8Array>();
  for (const knownId of knownPeerIds) {
    const knownIdentity = identities.get(knownId);
    if (!knownIdentity) throw new Error(`peer ${peerId} lists unknown peer ${knownId}`);
    knownPeers.set(knownId, knownIdentity.publicKey);
  }
  const keyring: MeshKeyring = {
    identity,
    knownPeers,
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
  return { identity, keyring, signaling, webrtc, mesh, repo, peerId };
}

async function shutdown(peer: Peer): Promise<void> {
  await peer.repo.shutdown();
  peer.signaling.close();
}

describe("MeshWebRTCAdapter convergence across join orderings", () => {
  test("late-join A-then-B: B joining second reaches A through peers-present", async () => {
    const docKey = generateDocumentKey();
    const identities = preGenerateIdentities(["peer-alpha", "peer-beta"]);
    // Peer ids chosen so "peer-beta" > "peer-alpha": the higher id is
    // the initiator under the tie-break rule, and we want B to be the
    // one whose handlePeersPresent fires the offer when it joins second.
    const a = buildPeer("peer-alpha", ["peer-beta"], docKey, identities);
    await a.signaling.connect();

    console.log("[test] A joined; verifying no peer before B arrives");
    await new Promise((r) => setTimeout(r, 300));
    expect(a.repo.peers.length).toBe(0);

    const b = buildPeer("peer-beta", ["peer-alpha"], docKey, identities);
    await b.signaling.connect();
    console.log("[test] B joined; waiting for WebRTC convergence");
    await waitFor(() => a.repo.peers.length > 0 && b.repo.peers.length > 0, 10000);

    const handleA = a.repo.create<Doc>({ title: "late-join-a-then-b", count: 1 });
    await handleA.whenReady();
    const handleB = await b.repo.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "late-join-a-then-b";
      } catch {
        return false;
      }
    }, 10000);
    expect(handleB.doc().count).toBe(1);

    handleB.change((d) => {
      d.count = 2;
    });
    await waitFor(() => handleA.doc().count === 2, 5000);
    expect(handleA.doc().count).toBe(2);

    await shutdown(a);
    await shutdown(b);
  });

  test("late-join B-then-A: A joining second reaches B through peer-joined", async () => {
    const docKey = generateDocumentKey();
    const identities = preGenerateIdentities(["peer-alpha", "peer-beta"]);
    const b = buildPeer("peer-beta", ["peer-alpha"], docKey, identities);
    await b.signaling.connect();

    console.log("[test] B joined first; verifying no peer before A arrives");
    await new Promise((r) => setTimeout(r, 300));
    expect(b.repo.peers.length).toBe(0);

    const a = buildPeer("peer-alpha", ["peer-beta"], docKey, identities);
    await a.signaling.connect();
    console.log("[test] A joined; waiting for WebRTC convergence");
    await waitFor(() => a.repo.peers.length > 0 && b.repo.peers.length > 0, 10000);

    const handleB = b.repo.create<Doc>({ title: "late-join-b-then-a", count: 10 });
    await handleB.whenReady();
    const handleA = await a.repo.find<Doc>(handleB.documentId);
    await waitFor(() => {
      try {
        return handleA.doc().title === "late-join-b-then-a";
      } catch {
        return false;
      }
    }, 10000);
    expect(handleA.doc().count).toBe(10);

    handleA.change((d) => {
      d.count = 11;
    });
    await waitFor(() => handleB.doc().count === 11, 5000);
    expect(handleB.doc().count).toBe(11);

    await shutdown(a);
    await shutdown(b);
  });

  test("simultaneous-join race: exactly one slot per pair, both directions work", async () => {
    const docKey = generateDocumentKey();
    const identities = preGenerateIdentities(["peer-alpha", "peer-beta"]);
    const a = buildPeer("peer-alpha", ["peer-beta"], docKey, identities);
    const b = buildPeer("peer-beta", ["peer-alpha"], docKey, identities);

    // Kick both joins in parallel — the server is free to process them
    // in either order, so we exercise the tie-break rule.
    await Promise.all([a.signaling.connect(), b.signaling.connect()]);
    console.log("[test] both signalling clients joined; waiting for WebRTC convergence");
    console.log(
      `[test] immediately after join: A slots=${a.webrtc.peerSlotCount()} B slots=${b.webrtc.peerSlotCount()}`
    );

    await waitFor(() => {
      const aPeers = a.repo.peers.length;
      const bPeers = b.repo.peers.length;
      const aSlots = a.webrtc.peerSlotCount();
      const bSlots = b.webrtc.peerSlotCount();
      if (aPeers > 0 && bPeers > 0) return true;
      if ((aSlots + bSlots) % 2 === 0 && aSlots + bSlots > 0) {
        // intentionally log the in-progress state once
      }
      return false;
    }, 10000);
    console.log(
      `[test] converged: A peers=${a.repo.peers.length} A slots=${a.webrtc.peerSlotCount()} B peers=${b.repo.peers.length} B slots=${b.webrtc.peerSlotCount()}`
    );

    // Give any glare resolution a moment to settle and then assert that
    // each side converged on exactly one slot for the other peer.
    await new Promise((r) => setTimeout(r, 300));
    expect(a.webrtc.peerSlotCount()).toBe(1);
    expect(b.webrtc.peerSlotCount()).toBe(1);

    const handleA = a.repo.create<Doc>({ title: "race", count: 100 });
    await handleA.whenReady();
    const handleB = await b.repo.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "race";
      } catch {
        return false;
      }
    }, 10000);
    expect(handleB.doc().count).toBe(100);

    await shutdown(a);
    await shutdown(b);
  });

  test("reconnect: a peer that closes and rejoins re-establishes its channel", async () => {
    const docKey = generateDocumentKey();
    // Reuse the same identities across A1 and A2 so the rejoin
    // genuinely looks like the same peer coming back, not a brand-new
    // device with a coincidentally reused peer id.
    const identities = preGenerateIdentities(["peer-alpha", "peer-beta"]);
    const a1 = buildPeer("peer-alpha", ["peer-beta"], docKey, identities);
    const b = buildPeer("peer-beta", ["peer-alpha"], docKey, identities);

    await a1.signaling.connect();
    await b.signaling.connect();
    await waitFor(() => a1.repo.peers.length > 0 && b.repo.peers.length > 0, 10000);

    const handleA1 = a1.repo.create<Doc>({ title: "reconnect", count: 0 });
    await handleA1.whenReady();
    const handleB = await b.repo.find<Doc>(handleA1.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "reconnect";
      } catch {
        return false;
      }
    }, 10000);

    console.log("[test] A disconnecting");
    await shutdown(a1);
    // Give the server's close handler time to propagate peer-left to B.
    await waitFor(() => b.webrtc.peerSlotCount() === 0, 5000);

    handleB.change((d) => {
      d.count = 42;
    });

    console.log("[test] reconnecting A as a fresh stack with the same peer id");
    const a2 = buildPeer("peer-alpha", ["peer-beta"], docKey, identities);
    await a2.signaling.connect();
    await waitFor(() => a2.repo.peers.length > 0 && b.repo.peers.length > 0, 10000);

    const handleA2 = await a2.repo.find<Doc>(handleA1.documentId);
    await waitFor(() => {
      try {
        return handleA2.doc().count === 42;
      } catch {
        return false;
      }
    }, 10000);
    expect(handleA2.doc().count).toBe(42);

    await shutdown(a2);
    await shutdown(b);
  });
});

done();
