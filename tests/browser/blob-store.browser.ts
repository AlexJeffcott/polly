/**
 * Browser test for the blob store end-to-end.
 *
 * Two peers run in the same browser tab. Peer A stores a blob locally and
 * announces it. Peer B requests it, receives the chunks over a real WebRTC
 * data channel, reassembles, verifies the hash, and caches locally.
 *
 * The blob store piggybacks on MeshWebRTCAdapter's data channel. This test
 * proves that chunked transfer, backpressure, reassembly, and hash
 * verification all work against real browser RTCDataChannel primitives —
 * not mocks.
 */

import { type PeerId, Repo } from "@automerge/automerge-repo";
import { computeBlobHash, createBlobRef } from "../../src/shared/lib/blob-ref";
import { createBlobStore } from "../../src/shared/lib/blob-store-impl";
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

describe("BlobStore end-to-end over WebRTC", () => {
  test("peer B downloads a blob from peer A via chunked transfer", async () => {
    console.log("[test] setting up keys");
    const aIdentity = generateSigningKeyPair();
    const bIdentity = generateSigningKeyPair();
    const docKey = generateDocumentKey();

    const aKeyring: MeshKeyring = {
      identity: aIdentity,
      knownPeers: new Map([["blob-peer-b", bIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };
    const bKeyring: MeshKeyring = {
      identity: bIdentity,
      knownPeers: new Map([["blob-peer-a", aIdentity.publicKey]]),
      documentKeys: new Map([[DEFAULT_MESH_KEY_ID, docKey]]),
      revokedPeers: new Set(),
    };

    console.log("[test] creating WebRTC adapters");
    const webrtcA = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient,
      peerId: "blob-peer-a",
      knownPeerIds: ["blob-peer-b"],
    });
    const signalingA = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "blob-peer-a",
      onSignal: (from, payload) => webrtcA.handleSignal(from, payload),
    });
    Object.assign(webrtcA, { signaling: signalingA });

    const webrtcB = new MeshWebRTCAdapter({
      signaling: null as unknown as MeshSignalingClient,
      peerId: "blob-peer-b",
      knownPeerIds: ["blob-peer-a"],
    });
    const signalingB = new MeshSignalingClient({
      url: SIGNALING_URL,
      peerId: "blob-peer-b",
      onSignal: (from, payload) => webrtcB.handleSignal(from, payload),
    });
    Object.assign(webrtcB, { signaling: signalingB });

    await signalingA.connect();
    await signalingB.connect();
    console.log("[test] signalling connected");

    // Wrap with crypto envelope for Automerge messages. The blob store
    // bypasses this layer and handles encryption directly via encrypt-then-chunk.
    const meshA = new MeshNetworkAdapter({ base: webrtcA, keyring: aKeyring });
    const meshB = new MeshNetworkAdapter({ base: webrtcB, keyring: bKeyring });

    const repoA = new Repo({ network: [meshA], peerId: "blob-peer-a" as unknown as PeerId });
    const repoB = new Repo({ network: [meshB], peerId: "blob-peer-b" as unknown as PeerId });

    // Wait for peer connection.
    console.log("[test] waiting for peer connection");
    await waitFor(() => repoA.peers.length > 0 && repoB.peers.length > 0, 10000);
    console.log(`[test] peers connected: A=${repoA.peers.length} B=${repoB.peers.length}`);

    // Create blob stores on each peer. Both use the same document key so
    // encrypt-then-chunk round-trips correctly.
    const blobsA = createBlobStore(webrtcA, { encrypt: { key: docKey } });
    const blobsB = createBlobStore(webrtcB, { encrypt: { key: docKey } });

    // Create a blob larger than a single chunk to exercise chunking.
    // 150 KiB = ~2.3 chunks at 64 KiB each.
    const originalBytes = new Uint8Array(150 * 1024);
    for (let i = 0; i < originalBytes.length; i++) {
      originalBytes[i] = i & 0xff;
    }
    const expectedHash = await computeBlobHash(originalBytes);
    const ref = await createBlobRef({
      bytes: originalBytes,
      filename: "test.bin",
      mimeType: "application/octet-stream",
    });
    console.log(`[test] blob size=${originalBytes.length} hash=${expectedHash.slice(0, 16)}...`);

    // Put blob on peer A. This caches locally and announces blob-have.
    await blobsA.put(ref, originalBytes);
    console.log("[test] blob stored on A, announcement sent");

    // Wait a moment for the blob-have announcement to reach B.
    await new Promise((r) => setTimeout(r, 500));

    // Peer B fetches the blob. Should request from A, receive chunks,
    // reassemble, decrypt, verify hash.
    console.log("[test] peer B fetching blob");
    const receivedBytes = await blobsB.get(ref.hash);
    console.log(`[test] received ${receivedBytes?.length ?? 0} bytes`);

    expect(receivedBytes).toBeDefined();
    if (!receivedBytes) throw new Error("blobsB.get returned undefined");
    expect(receivedBytes.length).toBe(originalBytes.length);

    // Verify byte-for-byte equality.
    let mismatch = -1;
    for (let i = 0; i < originalBytes.length; i++) {
      if (receivedBytes[i] !== originalBytes[i]) {
        mismatch = i;
        break;
      }
    }
    expect(mismatch).toBe(-1);

    // Verify hash.
    const actualHash = await computeBlobHash(receivedBytes);
    expect(actualHash).toBe(expectedHash);
    console.log("[test] bytes and hash verified");

    // A second get on B should hit the cache without any network traffic.
    const cached = await blobsB.get(ref.hash);
    expect(cached).toBeDefined();
    expect(cached?.length).toBe(originalBytes.length);

    // Cleanup.
    blobsA.dispose();
    blobsB.dispose();
    await repoA.shutdown();
    await repoB.shutdown();
    signalingA.close();
    signalingB.close();
    console.log("[test] done");
  });
});

done();
