/**
 * Browser test: createMeshClient round-trip.
 *
 * Unlike mesh-webrtc.browser.ts — which wires MeshSignalingClient,
 * MeshWebRTCAdapter, MeshNetworkAdapter, and Repo by hand — this test
 * builds two clients through the `createMeshClient` factory. The
 * factory is the documented entry point for consumer applications
 * (fairfox, lingua, any future mesh-backed app), so it has to be
 * tested end-to-end with real WebRTC and a real document mutation.
 *
 * The acceptance is a document written on client A converging on
 * client B via the CRDT sync protocol, both sides talking through
 * `createMeshClient`'s internal wiring. A previous version of the
 * factory omitted the `peerId` option when constructing the Repo,
 * which meant Automerge auto-generated a random id that didn't match
 * the mesh identity the `MeshNetworkAdapter` signed envelopes with;
 * verification silently dropped every sync message and this test
 * would have caught that by failing on non-convergence.
 *
 * Runs against the `signalingServer` Elysia plugin that
 * tools/test/src/browser/run.ts starts on an ephemeral port.
 */

import { generateDocumentKey } from "../../src/shared/lib/encryption";
import { createMeshClient } from "../../src/shared/lib/mesh-client";
import { DEFAULT_MESH_KEY_ID, type MeshKeyring } from "../../src/shared/lib/mesh-network-adapter";
import { generateSigningKeyPair } from "../../src/shared/lib/signing";
import { describe, done, expect, test, waitFor } from "../../tools/test/src/browser/harness";

const SIGNALING_URL = process.env.SIGNALING_URL ?? "ws://127.0.0.1:39000/polly/signaling";

interface Doc {
  title: string;
  count: number;
}

describe("createMeshClient end-to-end", () => {
  test("a document created on one client converges on its peer", async () => {
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();
    const peerA = "peer-client-a";
    const peerB = "peer-client-b";

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([[peerB, bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([[peerA, aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    const clientA = await createMeshClient({
      signaling: { url: SIGNALING_URL, peerId: peerA },
      keyring: aKeyring,
    });
    const clientB = await createMeshClient({
      signaling: { url: SIGNALING_URL, peerId: peerB },
      keyring: bKeyring,
    });

    await waitFor(() => clientA.repo.peers.length > 0 && clientB.repo.peers.length > 0, 10000);

    const handleA = clientA.repo.create<Doc>({ title: "factory-roundtrip", count: 1 });
    await handleA.whenReady();

    const handleB = await clientB.repo.find<Doc>(handleA.documentId);
    await waitFor(() => {
      try {
        return handleB.doc().title === "factory-roundtrip" && handleB.doc().count === 1;
      } catch {
        return false;
      }
    }, 10000);

    expect(handleB.doc().title).toBe("factory-roundtrip");
    expect(handleB.doc().count).toBe(1);

    handleB.change((d) => {
      d.count = 2;
    });
    await waitFor(() => handleA.doc().count === 2, 5000);
    expect(handleA.doc().count).toBe(2);

    await clientA.close();
    await clientB.close();
  });
});

done();
