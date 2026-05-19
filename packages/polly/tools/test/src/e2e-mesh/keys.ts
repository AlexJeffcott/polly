/**
 * @fairfox/polly/test/e2e-mesh — pre-baked keyring generation.
 *
 * E2e scripts that test the *drain* (offline-online, late-join, sync
 * recovery) need two peers who already know each other. The full pairing
 * ceremony is a separate surface tested by its own script; here we
 * pre-bake the keyrings so the script under test isn't paying the cost
 * of pairing on every run.
 *
 * The keys are real — the same generators production uses — so the
 * bootstrap path through `createMeshClient` is the same path a real user
 * takes. We just skip the UI ceremony.
 */

import { generateDocumentKey } from "../../../../src/shared/lib/encryption";
import { generateSigningKeyPair } from "../../../../src/shared/lib/signing";

export interface PrebakedPeer {
  peerId: string;
  /** base64-encoded identity secret key (64 bytes). */
  identitySecretKeyB64: string;
  /** base64-encoded identity public key (32 bytes). */
  identityPublicKeyB64: string;
}

export interface PrebakedKeyringPair {
  peers: [PrebakedPeer, PrebakedPeer];
  /** base64-encoded shared document key for the default mesh key id. */
  docKeyB64: string;
}

function toBase64(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i] as number);
  }
  return btoa(binary);
}

/**
 * Build two peers that already know each other and share a document key.
 * Peer ids default to "peer-a" / "peer-b" — override if a script needs
 * specific ids for log readability.
 */
export function prebakeKeyringPair(peerIdA = "peer-a", peerIdB = "peer-b"): PrebakedKeyringPair {
  const set = prebakeKeyringSet([peerIdA, peerIdB]);
  return {
    peers: [set.peers[0] as PrebakedPeer, set.peers[1] as PrebakedPeer],
    docKeyB64: set.docKeyB64,
  };
}

export interface PrebakedKeyringSet {
  /** Every peer in the set, each carrying its own identity. */
  peers: PrebakedPeer[];
  /** Shared document key for the default mesh key id. */
  docKeyB64: string;
}

/**
 * Build N peers that all know each other and share a single document
 * key. Use when a script needs more than two endpoints — three-peer
 * convergence, revocation-over-wire, multi-hop.
 *
 * The result is symmetric: every peer's keyring contains the public
 * keys of every other peer. Scripts that want to test asymmetric
 * topologies (a peer that knows a subset) thin out the knownPeers map
 * per-peer when wiring the bootstrap.
 */
export function prebakeKeyringSet(peerIds: ReadonlyArray<string>): PrebakedKeyringSet {
  if (peerIds.length < 2) {
    throw new Error("prebakeKeyringSet: at least two peer ids required");
  }
  const docKey = generateDocumentKey();
  const peers: PrebakedPeer[] = peerIds.map((peerId) => {
    const pair = generateSigningKeyPair();
    return {
      peerId,
      identitySecretKeyB64: toBase64(pair.secretKey),
      identityPublicKeyB64: toBase64(pair.publicKey),
    };
  });
  return { peers, docKeyB64: toBase64(docKey) };
}

/**
 * Build the `knownPeers` map a single peer's bootstrap needs: every
 * other peer in the set, keyed by peerId, valued by the base64 public
 * key. Scripts call this per peer when wiring `serveConsumer({
 * bootstrap: { ..., knownPeers: knownPeersFor(set, "peer-a") } })`.
 */
export function knownPeersFor(set: PrebakedKeyringSet, thisPeerId: string): Record<string, string> {
  const out: Record<string, string> = {};
  for (const peer of set.peers) {
    if (peer.peerId === thisPeerId) continue;
    out[peer.peerId] = peer.identityPublicKeyB64;
  }
  return out;
}
