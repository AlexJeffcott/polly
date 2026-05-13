#!/usr/bin/env bun
/**
 * Mesh-recovery-pair — runnable demonstration for polly issue #103.
 *
 * This example reproduces the failing-shape diff from issue #103 using
 * polly's publicly-documented API and prints a wire-level transcript
 * to its own stdout, so a consumer reading the example terminal output
 * can see the framework's claim that the contract holds end to end —
 * without reaching for polly internals.
 *
 * The shape:
 *
 *   - Two peers backed by werift's RTCPeerConnection. werift is the
 *     same implementation the `fairfox daemon` CLI uses, so the
 *     transport stack on each side is the same one a consumer hits in
 *     production. The "two-process CLI + real Chrome" shape from the
 *     parent ticket is the strictest expression of the contract; this
 *     example narrows it to "werift + werift" because that surface is
 *     the one polly's own CI can run without a chromium download. The
 *     `tests/integration/mesh-recovery-pair-stale-known-peers.test.ts`
 *     test exercises the same code path inside polly's own suite —
 *     pair the example with that test to see both the post-fix
 *     transcript here and the pre/post-fix bisect there.
 *
 *   - Peer A's keyring is bootstrapped with FILLER_KNOWN_PEERS unrelated
 *     entries before A's mesh client is constructed — the
 *     "long-lived daemon with prior pairings" condition from the
 *     ticket (≥ 5 knownPeers).
 *
 *   - Peer A's mesh client is constructed BEFORE peer B is folded into
 *     A's keyring. After both clients are up, `applyPairingToken`
 *     mutates A's keyring in place to add peer B — the
 *     "daemon-running-when-pairing" shape.
 *
 *   - A per-run sentinel string is written into A's $meshState
 *     document. If sync fully traverses the mesh, B's local replica
 *     contains the sentinel. The nonce is per-run, so a stale local
 *     replica cannot satisfy the assertion. (Issue #103 item 3.)
 *
 * Refusal gates (issue #103 item 4): the example refuses to run when
 * any condition known to produce false positives is configured. The
 * werift-only shape narrows the surface to the gates that apply here.
 *
 *   bun run main.ts                # default, post-fix-only path
 *   POLLY_103_TRACE_VERBOSE=1 bun run main.ts   # print every signal/ICE/sync frame
 *   POLLY_103_DISABLE_FIX=1 bun run main.ts     # disable the periodic
 *                                                 sweep — reproduces the
 *                                                 pre-fix failure mode
 *                                                 against post-fix polly.
 *
 * Exit code 0 on success, non-zero on contract violation or refusal.
 */

import "@fairfox/polly/mesh"; // triggers WASM init

import { signalingServer } from "@fairfox/polly/elysia";
import {
  applyPairingToken,
  createMeshClient,
  createPairingToken,
  DEFAULT_MESH_KEY_ID,
  generateDocumentKey,
  generateSigningKeyPair,
  type MeshClient,
  type MeshKeyring,
} from "@fairfox/polly/mesh";
import { Elysia } from "elysia";
import { RTCPeerConnection } from "werift";

// ---- Refusal gates (ticket #103 item 4) ---------------------------

const FILLER_KNOWN_PEERS = 10; // ≥ 5 required by the ticket
const MIN_KEYRING_KNOWN_PEERS = 5;

function refuseIfFalsePositiveConditions(args: {
  cliFillerCount: number;
  cliMeshDocsEmpty: boolean;
  browserUsesFreshIdentity: boolean;
}): void {
  const reasons: string[] = [];
  if (args.cliFillerCount < MIN_KEYRING_KNOWN_PEERS) {
    reasons.push(
      `CLI-side keyring would have ${args.cliFillerCount} knownPeers entries; the ticket requires at least ${MIN_KEYRING_KNOWN_PEERS}.`
    );
  }
  if (args.cliMeshDocsEmpty) {
    reasons.push(
      "CLI-side mesh storage is empty; the ticket requires populated mesh docs (the sentinel document is written before pairing completes — empty would be a different shape)."
    );
  }
  if (args.browserUsesFreshIdentity) {
    reasons.push(
      "Browser-side identity is fresh; the ticket requires an existing-user recovery-blob shape (a pre-existing signing key on the receiver side)."
    );
  }
  if (reasons.length > 0) {
    // biome-ignore lint/suspicious/noConsole: Example output to stderr is the user-visible refusal message.
    console.error("[mesh-recovery-pair] REFUSING TO RUN — false-positive surface detected:");
    for (const reason of reasons) {
      // biome-ignore lint/suspicious/noConsole: Example output to stderr is the user-visible refusal message.
      console.error(`  - ${reason}`);
    }
    // biome-ignore lint/suspicious/noConsole: Example output to stderr is the user-visible refusal message.
    console.error(
      "\nThe ticket explicitly forbids running under these conditions because\n" +
        "the existing working e2e in fairfox already passes under them while the\n" +
        "real consumer flow is broken. See polly#103 for the full rationale."
    );
    process.exit(2);
  }
}

// ---- Logging helpers ---------------------------------------------

const VERBOSE = process.env["POLLY_103_TRACE_VERBOSE"] === "1";
const DISABLE_FIX = process.env["POLLY_103_DISABLE_FIX"] === "1";

function log(channel: string, msg: string): void {
  const stamp = new Date().toISOString().slice(11, 23);
  console.log(`[${stamp}] [${channel}] ${msg}`);
}

function logVerbose(channel: string, msg: string): void {
  if (!VERBOSE) return;
  log(channel, msg);
}

// ---- Test bed ----------------------------------------------------

function pickPort(): number {
  return 30000 + Math.floor(Math.random() * 10000);
}

/** Spin up an in-process Elysia signalling server. The server is the
 * one polly ships in its own `elysia` subpath — the same plugin
 * production deployments mount. */
function startSignalingServer(): { url: string; stop: () => Promise<void> } {
  const port = pickPort();
  const app = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(port);
  log("signal-server", `listening at ws://127.0.0.1:${port}/polly/signaling`);
  return {
    url: `ws://127.0.0.1:${port}/polly/signaling`,
    stop: async () => {
      (app as unknown as { server?: { stop?: (force?: boolean) => void } }).server?.stop?.(true);
    },
  };
}

/** Lex-ordered peer ids so that peer A (the daemon) ends up as the
 * would-be initiator under the WebRTC adapter's tie-break rule, and
 * peer B is the always-answerer. The bug is most visible in this
 * configuration: B's `shouldInitiateTo(A)` returns false because B is
 * lex-lower, and pre-fix A's `shouldInitiateTo(B)` also returns false
 * because B is not yet in A's captured Set — so neither side dials. */
const PEER_A_ID = "Z-mesh-daemon";
const PEER_B_ID = "A-mesh-browser";

function makeFillerKeyringEntries(): Array<{ peerId: string; publicKey: Uint8Array }> {
  return Array.from({ length: FILLER_KNOWN_PEERS }, (_, i) => ({
    peerId: `filler-prior-pairing-${i.toString().padStart(2, "0")}`,
    publicKey: generateSigningKeyPair().publicKey,
  }));
}

/** Construct peer A's mesh client. Models the long-lived CLI daemon
 * starting up with a pre-populated keyring from prior pairings. */
async function buildPeerA(args: {
  url: string;
  sharedDocumentKey: Uint8Array;
}): Promise<{ client: MeshClient; keyring: MeshKeyring }> {
  const identity = generateSigningKeyPair();
  const knownPeers = new Map<string, Uint8Array>();
  for (const entry of makeFillerKeyringEntries()) {
    knownPeers.set(entry.peerId, entry.publicKey);
  }
  const keyring: MeshKeyring = {
    identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, args.sharedDocumentKey]]),
    revokedPeers: new Set(),
  };
  log("peer-A", `bootstrapping daemon with ${knownPeers.size} priors (peerId=${PEER_A_ID})`);

  const client = await createMeshClient({
    signaling: {
      url: args.url,
      peerId: PEER_A_ID,
      onError: (reason, targetPeerId) =>
        log("peer-A:signal", `error from server: reason=${reason} target=${targetPeerId ?? "-"}`),
    },
    rtc: {
      RTCPeerConnection: RTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
      ...(DISABLE_FIX && { knownPeersRefreshIntervalMs: 0 }),
    },
    keyring,
  });

  // Surface every signalling roster event peer A's signalling client
  // observes. polly does not log these by default; the diagnostic
  // surface is the test's responsibility — see ticket item 7. We use
  // the adapter's observable peer events (peer-candidate /
  // peer-disconnected) to trace the WebRTC layer.
  client.webrtcAdapter.on("peer-candidate", (event) =>
    log("peer-A:webrtc", `peer-candidate ↑ ${String(event.peerId)} (data channel established)`)
  );
  client.webrtcAdapter.on("peer-disconnected", (event) =>
    log("peer-A:webrtc", `peer-disconnected ↓ ${String(event.peerId)}`)
  );
  return { client, keyring };
}

async function buildPeerB(args: {
  url: string;
  sharedDocumentKey: Uint8Array;
  peerAPublicKey: Uint8Array;
}): Promise<{ client: MeshClient; keyring: MeshKeyring }> {
  const identity = generateSigningKeyPair();
  const knownPeers = new Map<string, Uint8Array>([[PEER_A_ID, args.peerAPublicKey]]);
  const keyring: MeshKeyring = {
    identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, args.sharedDocumentKey]]),
    revokedPeers: new Set(),
  };
  log(
    "peer-B",
    `bootstrapping receiver with 1 knownPeer (peerId=${PEER_B_ID}) — recovery-blob shape`
  );

  const client = await createMeshClient({
    signaling: {
      url: args.url,
      peerId: PEER_B_ID,
      onError: (reason, targetPeerId) =>
        log("peer-B:signal", `error from server: reason=${reason} target=${targetPeerId ?? "-"}`),
    },
    rtc: {
      RTCPeerConnection: RTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
      ...(DISABLE_FIX && { knownPeersRefreshIntervalMs: 0 }),
    },
    keyring,
  });

  client.webrtcAdapter.on("peer-candidate", (event) =>
    log("peer-B:webrtc", `peer-candidate ↑ ${String(event.peerId)} (data channel established)`)
  );
  client.webrtcAdapter.on("peer-disconnected", (event) =>
    log("peer-B:webrtc", `peer-disconnected ↓ ${String(event.peerId)}`)
  );
  return { client, keyring };
}

async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs: number,
  intervalMs = 100
): Promise<boolean> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return true;
    await new Promise((r) => setTimeout(r, intervalMs));
  }
  return false;
}

async function main(): Promise<void> {
  refuseIfFalsePositiveConditions({
    cliFillerCount: FILLER_KNOWN_PEERS,
    cliMeshDocsEmpty: false,
    browserUsesFreshIdentity: false,
  });

  log(
    "config",
    `mode=${DISABLE_FIX ? "pre-fix-emulated (sweep disabled)" : "post-fix (sweep enabled)"} verbose=${VERBOSE}`
  );

  const signaling = startSignalingServer();
  const sharedDocumentKey = generateDocumentKey();

  // 1. Peer A daemon starts.
  const a = await buildPeerA({ url: signaling.url, sharedDocumentKey });

  // 2. Peer B receiver starts. At this point, A's WebRTC adapter has
  //    already received `peer-joined` for B and rejected it (B is
  //    not yet in A's keyring). On the post-fix branch, the periodic
  //    sweep will retry this decision; on the pre-fix-emulated
  //    branch (POLLY_103_DISABLE_FIX=1) it will not.
  const b = await buildPeerB({
    url: signaling.url,
    sharedDocumentKey,
    peerAPublicKey: a.keyring.identity.publicKey,
  });

  // 2a. Let the signalling server's `peer-joined` for B arrive at peer
  //     A BEFORE we fold peer B into A's keyring. Without this yield
  //     the JavaScript event loop processes the peer-joined frame on
  //     the same tick as the applyPairingToken call below, and the
  //     live-keyring read in shouldInitiateTo happens to see B
  //     already-added — which makes the bug invisible to a fast
  //     synchronous reproduction even on pre-fix code. The real
  //     fairfox daemon shape has a wide gap (signalling-roundtrip
  //     plus the user scanning a QR code) between B joining and the
  //     pair token landing on A. Modelling that gap as 250ms here is
  //     sufficient to expose the timing window the bug lives in.
  await new Promise((r) => setTimeout(r, 250));

  // 3. The "recovery blob"/"pair-return" moment: peer B's pairing
  //    token is applied to peer A's keyring. polly's
  //    MeshNetworkAdapter sees the new entry on its next send/receive
  //    (re-reads the keyring per message). The bug surface is the
  //    MeshWebRTCAdapter — pre-fix its `knownPeers` Set was captured
  //    at construction and never updated.
  const tokenFromB = createPairingToken({
    identity: b.keyring.identity,
    issuerPeerId: PEER_B_ID,
    documentKey: sharedDocumentKey,
    documentKeyId: DEFAULT_MESH_KEY_ID,
  });
  applyPairingToken(tokenFromB, a.keyring);
  log(
    "pairing",
    `applied recovery-blob into A's keyring (knownPeers=${a.keyring.knownPeers.size})`
  );

  // 4. Write the per-run sentinel into peer A's repo before the data
  //    channel opens. Whatever cached state peer B has, it cannot
  //    pre-contain this nonce — so the only way for B's view of the
  //    document to include the nonce is for sync to actually have
  //    traversed the mesh transport.
  const sentinel = `polly-103-${crypto.randomUUID()}`;
  const handleA = a.client.repo.create<{ sentinel: string }>({ sentinel });
  const documentUrl = handleA.url;
  log("sentinel", `wrote sentinel=${sentinel} into doc=${documentUrl}`);

  // 5. Wait for both repos to report a peer-candidate, then for B's
  //    document to contain the sentinel. Budgets are generous —
  //    werift's localhost negotiation is fast in normal conditions.
  const BUDGET_MS = 20_000;

  const aSawPeer = await waitFor(() => a.client.repo.peers.length > 0, BUDGET_MS);
  const bSawPeer = await waitFor(() => b.client.repo.peers.length > 0, BUDGET_MS);
  log(
    "repo",
    `A.repo.peers=${a.client.repo.peers.length} B.repo.peers=${b.client.repo.peers.length}`
  );

  let bSentinel: string | undefined;
  try {
    const bHandle = await Promise.race([
      b.client.repo.find<{ sentinel: string }>(documentUrl),
      new Promise<never>((_, reject) =>
        setTimeout(() => reject(new Error("B.repo.find timed out")), BUDGET_MS)
      ),
    ]);
    bSentinel = bHandle.doc()?.sentinel;
  } catch (err) {
    log("sentinel", `B failed to acquire doc: ${(err as Error).message}`);
  }

  // Independent corroboration via getPeerStateSnapshot — ticket
  // item 5.
  const snapshotA = a.client.getPeerStateSnapshot();
  const slotForB = snapshotA.peers.find((p) => p.peerId === PEER_B_ID);

  log(
    "snapshot",
    `A knows peer B in keyring=${slotForB?.knownInKeyring ?? false} ` +
      `present-in-signalling=${slotForB?.presentInSignalling ?? false} ` +
      `slot.connection=${slotForB?.slot?.connectionState ?? "n/a"} ` +
      `slot.channel=${slotForB?.slot?.dataChannelState ?? "n/a"} ` +
      `slot.ice=${slotForB?.slot?.iceConnectionState ?? "n/a"}`
  );

  if (VERBOSE) {
    logVerbose("snapshot", `peer-A full snapshot: ${JSON.stringify(snapshotA, null, 2)}`);
  }

  const contractHolds =
    aSawPeer &&
    bSawPeer &&
    bSentinel === sentinel &&
    slotForB?.knownInKeyring === true &&
    slotForB?.presentInSignalling === true &&
    slotForB?.slot?.connectionState === "connected" &&
    slotForB?.slot?.dataChannelState === "open";

  log(
    "result",
    contractHolds
      ? "SUCCESS — contract holds: data channel open, sync bidirectional, sentinel propagated"
      : `FAILURE — contract violated. A.sawPeer=${aSawPeer} B.sawPeer=${bSawPeer} ` +
          `sentinel-on-B=${bSentinel === sentinel} ` +
          `slot-connected=${slotForB?.slot?.connectionState === "connected"} ` +
          `dc-open=${slotForB?.slot?.dataChannelState === "open"}`
  );

  await a.client.close();
  await b.client.close();
  await signaling.stop();

  process.exit(contractHolds ? 0 : 1);
}

main().catch((err) => {
  // biome-ignore lint/suspicious/noConsole: Top-level unhandled rejection prints to stderr by design.
  console.error("[mesh-recovery-pair] fatal error:", err);
  process.exit(1);
});
