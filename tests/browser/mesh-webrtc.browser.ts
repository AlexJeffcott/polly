/**
 * Browser test for MeshWebRTCAdapter end-to-end.
 *
 * Two peers run in the same browser tab. Each has its own
 * MeshSignalingClient, MeshWebRTCAdapter, MeshNetworkAdapter (for
 * signing + encryption), and Automerge Repo. They connect through a
 * real signalling server running on the Bun side (injected via
 * process.env.SIGNALING_URL at bundle time).
 *
 * The test proves: a document created on peer A propagates to peer B
 * through actual WebRTC data channels, signed and encrypted at the
 * wire level. This is the same stack a production $meshState
 * application uses.
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

// The signalling URL is injected by the runner via Bun.build define.
const SIGNALING_URL = process.env.SIGNALING_URL ?? "ws://127.0.0.1:39000/polly/signaling";

type Doc = {
  title: string;
  count: number;
};

describe("MeshWebRTCAdapter end-to-end in a real browser", () => {
  test("two peers exchange a document through WebRTC data channels", async () => {
    console.log("[test] setting up keys");
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    // Build two adapters. Each needs its own signalling client because
    // each registers under a different peer id.
    console.log("[test] connecting signalling clients");

    // Peer A's adapter — we construct it first, wire handleSignal later
    const webrtcA = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient, // wired below
      peerId: "peer-a",
      knownPeerIds: ["peer-b"],
    });

    const signalingA = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "peer-a",
      onSignal: (from, payload) => webrtcA.handleSignal(from, payload),
    });

    // Replace the signaling reference via Object.assign since the field is readonly
    Object.assign(webrtcA, { signaling: signalingA });

    const webrtcB = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient,
      peerId: "peer-b",
      knownPeerIds: ["peer-a"],
    });

    const signalingB = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "peer-b",
      onSignal: (from, payload) => webrtcB.handleSignal(from, payload),
    });
    Object.assign(webrtcB, { signaling: signalingB });

    // Connect both signalling clients.
    await signalingA.connect();
    await signalingB.connect();
    console.log("[test] signalling connected");

    // Wrap each WebRTC adapter with the crypto envelope.
    const meshA = new MeshNetworkAdapter({ base: webrtcA, keyring: aKeyring });
    const meshB = new MeshNetworkAdapter({ base: webrtcB, keyring: bKeyring });

    // Build Repos.
    const repoA = new Repo({ network: [meshA], peerId: "peer-a" as PeerId });
    const repoB = new Repo({ network: [meshB], peerId: "peer-b" as PeerId });

    // Wait for the WebRTC peer connection to establish.
    console.log("[test] waiting for peer connection");
    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0, 10000);
    console.log(`[test] peers connected: A=${repoA.peers.length} B=${repoB.peers.length}`);

    // Create a document on A.
    const handleA = repoA.create<Doc>({ title: "browser-test", count: 42 });
    await handleA.whenReady();
    console.log(`[test] doc created on A: ${handleA.documentId}`);

    // Wait for B to receive it.
    const handleB = await repoB.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "browser-test";
      } catch {
        return false;
      }
    }, 10000);
    console.log("[test] doc received on B");

    expect(handleB.doc().title).toBe("browser-test");
    expect(handleB.doc().count).toBe(42);

    // Mutate on B, verify A sees it.
    handleB.change((doc) => {
      doc.count = 99;
    });
    await waitFor(() => {
      try {
        return handleA.doc().count === 99;
      } catch {
        return false;
      }
    }, 5000);
    console.log("[test] mutation propagated back to A");

    expect(handleA.doc().count).toBe(99);

    // Cleanup.
    await repoA.shutdown();
    await repoB.shutdown();
    signalingA.close();
    signalingB.close();
    console.log("[test] done");
  });
});

done();
