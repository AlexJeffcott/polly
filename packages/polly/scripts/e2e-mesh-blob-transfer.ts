#!/usr/bin/env bun
/**
 * E2e: blob transfer from cold state.
 *
 * `createBlobStore` is the encrypt → chunk → announce → request → decrypt →
 * hash-verify pipeline that backs peer-to-peer file sharing. It is the
 * surface the `examples/blob-share` app demonstrates and unit tests cover
 * in pieces, but nothing drives the whole pipeline across two real peers
 * over real WebRTC from cold state. A regression in the chunking or the
 * hash-verify step would pass every unit test and only surface when a user
 * actually sent a file.
 *
 * Scenario: two prebaked peers connect over a fresh relay. Peer A stores a
 * blob — a deterministic ~48 KiB payload, large enough to exercise
 * multi-chunk transfer rather than a single-frame fast path. The blob store
 * announces `blob-have` to peer B. Peer B fetches the blob by its content
 * hash and the script asserts the bytes round-trip exactly: same length,
 * same content, and the receiver's hash matches the sender's. Because the
 * store hash-verifies on receipt, a corrupted or truncated transfer would
 * surface as a `get` that never resolves (timeout) rather than wrong bytes.
 *
 * The keyring is prebaked here on purpose — the pairing ceremony has its
 * own script; this one isolates the blob pipeline.
 */

export const capability = "mesh.blob-transfer" as const;

import {
  knownPeersFor,
  type LaunchedPeer,
  launchPeer,
  prebakeKeyringSet,
  type ServeConsumerResult,
  serveConsumer,
  waitForMeshConnected,
  withRelay,
} from "../tools/test/src/e2e-mesh";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const SETTLE_MS = 2_000;
const BLOB_SIZE = 48 * 1024;
const GET_TIMEOUT_MS = 20_000;

/** Build a deterministic payload so the assertion can compare exact bytes
 *  without sharing the buffer between peers (they run in separate browsers). */
function makePayload(size: number): Uint8Array {
  const bytes = new Uint8Array(size);
  for (let i = 0; i < size; i++) {
    bytes[i] = (i * 31 + 7) & 0xff;
  }
  return bytes;
}

function toBase64(bytes: Uint8Array): string {
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary);
}

function fromBase64(b64: string): Uint8Array {
  const binary = atob(b64);
  const out = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    out[i] = binary.charCodeAt(i);
  }
  return out;
}

/** Put a blob on the sender and return its content hash. */
async function putBlob(peer: LaunchedPeer, bytesB64: string): Promise<string> {
  const hash = await peer.page.evaluate(async (b64) => {
    const fn = (
      window as unknown as {
        __pollyE2eBlobPut?: (b: string, name: string, mime: string) => Promise<string>;
      }
    ).__pollyE2eBlobPut;
    if (!fn) throw new Error("__pollyE2eBlobPut hook missing");
    return fn(b64, "payload.bin", "application/octet-stream");
  }, bytesB64);
  if (!hash) throw new Error(`putBlob(${peer.peerId}): empty hash`);
  return hash;
}

/** Poll the receiver until the blob arrives, returning its base64 bytes. */
async function getBlob(peer: LaunchedPeer, hash: string, timeoutMs: number): Promise<string> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    const result = await peer.page.evaluate(async (h) => {
      const fn = (
        window as unknown as { __pollyE2eBlobGet?: (h: string) => Promise<string | null> }
      ).__pollyE2eBlobGet;
      if (!fn) throw new Error("__pollyE2eBlobGet hook missing");
      return fn(h);
    }, hash);
    if (result) return result;
    await new Promise((r) => setTimeout(r, 200));
  }
  throw new Error(
    `getBlob(${peer.peerId}): blob ${hash.slice(0, 12)}… did not arrive in ${timeoutMs}ms`
  );
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const relay = await withRelay();
  const keys = prebakeKeyringSet(["peer-a", "peer-b"]);

  const servers: ServeConsumerResult[] = [];
  const peers: LaunchedPeer[] = [];

  const cleanup = async () => {
    for (const peer of peers) await peer.close();
    for (const server of servers) await server.close();
    await relay.close();
  };

  try {
    for (const peer of keys.peers) {
      const server = await serveConsumer({
        bootstrap: {
          peerId: peer.peerId,
          signalingUrl: relay.url,
          identitySecretKeyB64: peer.identitySecretKeyB64,
          knownPeers: knownPeersFor(keys, peer.peerId),
          docKeyB64: keys.docKeyB64,
          blobMode: true,
        },
      });
      servers.push(server);

      const launched = await launchPeer({ peerId: peer.peerId, consumerUrl: server.url });
      peers.push(launched);
    }

    const [peerA, peerB] = peers;
    if (peerA === undefined || peerB === undefined) {
      throw new Error("test setup: expected two launched peers");
    }
    ctx.log("[e2e] both peers launched; waiting for mesh handshake");
    await waitForMeshConnected(peers, { timeoutMs: 15_000 });
    await new Promise((r) => setTimeout(r, SETTLE_MS));

    const payload = makePayload(BLOB_SIZE);
    const payloadB64 = toBase64(payload);
    ctx.log(`[e2e] peer A stores a ${BLOB_SIZE}-byte blob`);
    const hash = await putBlob(peerA, payloadB64);
    ctx.log(`[e2e] blob stored as ${hash.slice(0, 16)}…; peer B fetching`);

    // Falsification gate: fetch a hash that was never stored on any peer.
    // No peer can satisfy the request, so `get` must time out and the
    // script must FAIL — proof that the pass depends on a real transfer.
    const fetchHash =
      process.env["FALSIFY_WRONG_HASH"] === "1" ? `${hash.slice(0, -1)}0deadbeef` : hash;
    const receivedB64 = await getBlob(peerB, fetchHash, GET_TIMEOUT_MS);
    const received = fromBase64(receivedB64);

    if (received.length !== payload.length) {
      throw new Error(`length mismatch: sent ${payload.length}, received ${received.length}`);
    }
    for (let i = 0; i < payload.length; i++) {
      if (received[i] !== payload[i]) {
        throw new Error(
          `byte mismatch at offset ${i}: sent ${payload[i]}, received ${received[i]}`
        );
      }
    }

    // The receiver re-derives the hash and the store hash-verifies on
    // receipt; an equal round-trip plus a matching hash confirms the
    // encrypt/chunk/verify pipeline end to end.
    const receivedHash = await peerB.page.evaluate(async (b64) => {
      const fn = (
        window as unknown as {
          __pollyE2eBlobPut?: (b: string, name: string, mime: string) => Promise<string>;
        }
      ).__pollyE2eBlobPut;
      if (!fn) throw new Error("__pollyE2eBlobPut hook missing");
      return fn(b64, "payload.bin", "application/octet-stream");
    }, receivedB64);
    if (receivedHash !== hash) {
      throw new Error(`hash mismatch: sent ${hash}, receiver re-derived ${receivedHash}`);
    }

    ctx.log("[e2e] bytes round-tripped exactly and hash matches; final assertions");
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
