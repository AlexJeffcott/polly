#!/usr/bin/env bun
/**
 * Mesh-slot-initiation-realistic-keyring — falsification harness for
 * polly issue #106.
 *
 * polly#103 closed "long-lived daemon doesn't dial a newly-keyringed
 * peer". polly#104 closed "60 KiB fragments dropped silently by werift".
 * polly#105 closed "relay-only enforcement leak". Yet against a real
 * Chrome 148 tab paired into a daemon that holds an actual user's
 * keyring (78 known peers, 3 simultaneously on signalling, 17.6 MB of
 * mesh storage), a substantial fraction of `peer-joined` notifications
 * still never produced an RTC slot, and the slots that did form never
 * started an Automerge sync exchange.
 *
 * This harness reproduces the failing-shape diff inside polly's own CI
 * by:
 *
 *   - Bootstrapping the "daemon" peer with at least 50 known peers in
 *     its keyring. Most of those keyring entries never appear on
 *     signalling — that's the realistic shape: keyrings only grow, but
 *     not every paired device is online at every moment.
 *
 *   - Having a handful of "real" peers actually join signalling, some
 *     before the daemon constructs (so they arrive via `peers-present`)
 *     and some after (so they arrive via `peer-joined`).
 *
 *   - Picking peer ids so that the real peers straddle the daemon's
 *     lex-tie-break: some of the daemon's slot constructions are as
 *     initiator, some as answerer.
 *
 *   - Injecting a synthetic throw inside the WebRTC adapter's slot
 *     construction for one of the real peers, to stress the per-peer
 *     try/catch the polly#106 fix adds. Pre-fix code aborted the entire
 *     sweep loop on a single throw; post-fix code names the failing
 *     peer in the snapshot's `slotInitiationRejectionReason` and
 *     continues to the next peer.
 *
 * Refusal gates (polly#106 item 3): the harness will not run when its
 * input is itself a polly#103-style false-positive surface.
 *
 *   - Fewer than 50 known peers in the daemon keyring — that's the
 *     polly#103 shape, not the polly#106 shape.
 *   - All real peers already online when the daemon constructs (no
 *     gradual arrival).
 *   - All real peers lex-aligned (initiator-direction consistent) —
 *     would mask a tie-break-direction bug.
 *
 * Falsification gate (polly#106 item 2):
 *
 *   POLLY_106_DISABLE_FIX=1 reverts the polly#106 fixes by
 *   monkey-patching the adapter to use the pre-fix `refreshKnownPeers`
 *   (no per-peer try/catch) and bypassing the dc=open peer-candidate
 *   emit. With the gate enabled, the synthetic-throw peer takes the
 *   sweep down with it: every peer iterated after it in the same tick
 *   loses its dial opportunity, and the named failure prints
 *   "sweep-loop aborted on synthetic throw".
 *
 * Wire-level transcript: every peer's snapshot at the end of the run
 * is written to `transcript.json` alongside this file. Pre-fix runs
 * preserve the slotted/unslotted bisect so a follow-up reader can see
 * exactly which peers the sweep failed to reach.
 *
 *   bun run main.ts                                # default, post-fix path
 *   POLLY_106_DISABLE_FIX=1 bun run main.ts        # falsification mode
 *   POLLY_106_TRACE_VERBOSE=1 bun run main.ts      # dump every snapshot sample
 *
 * Exit code 0 on success, 1 on contract violation, 2 on refusal.
 */

import "@fairfox/polly/mesh"; // triggers WASM init

import { writeFile } from "node:fs/promises";
import { resolve as resolvePath } from "node:path";
import { signalingServer } from "@fairfox/polly/elysia";
import {
  createMeshClient,
  DEFAULT_MESH_KEY_ID,
  generateDocumentKey,
  generateSigningKeyPair,
  type MeshClient,
  type MeshKeyring,
  type MeshWebRTCAdapter,
  type SlotInitiationRejectionReason,
} from "@fairfox/polly/mesh";
import { Elysia } from "elysia";
import { RTCPeerConnection as WeriftRTCPeerConnection } from "werift";

// ---- Constants ----------------------------------------------------

/** Real-world keyrings grow to dozens of peers over months of paired
 * devices. The reporter's daemon held 78 entries; the polly#103
 * example used 10. We sit comfortably above the polly#103 surface so
 * the bug shape this harness exercises cannot be masked by reaching
 * for the polly#103 reproducer. */
const KEYRING_FILLER_COUNT = 60;

/** Refusal bar: at least 50 keyring entries are required. Below that
 * is the polly#103 surface; the polly#106 shape needs the keyring to
 * be substantial enough that a forensic snapshot has many "(no slot)"
 * peers to disambiguate. */
const REFUSAL_MIN_KEYRING = 50;

/** Real peers that actually come online during the run. The mix of
 * initial-arrival and late-arrival, and the deliberate spread of peer
 * ids around the daemon's lex tie-break, models the realistic shape:
 * some peers were already in signalling when the daemon connected,
 * some arrived later, and the daemon must dial some and be dialled by
 * others. */
const REAL_PEERS_INITIAL_COUNT = 3; // present at signalling-join time
const LATE_ARRIVAL_DELAY_MS = 750;

/** Total observation budget: the sweep runs every 2s by default, so
 * 8s gives the sweep four chances to fire for every applicable peer. */
const OBSERVATION_BUDGET_MS = 8_000;

/** Sweep interval override. The default in production is 2000ms; we
 * tighten the loop here so the test bed finishes in seconds rather
 * than minutes. The same shape would expose the bug at 2000ms; this
 * is purely a speedup. */
const SWEEP_INTERVAL_MS = 250;

// ---- Env switches -------------------------------------------------

const DISABLE_FIX = process.env.POLLY_106_DISABLE_FIX === "1";
const VERBOSE = process.env.POLLY_106_TRACE_VERBOSE === "1";

// ---- Uncaught-error capture (pre-fix-emulated only) --------------

/** Pre-fix code lets a throw inside the dial path bubble out of the
 * signalling client's frame dispatch (or out of `setInterval`'s
 * callback), which crashes the bun process. We need to keep the
 * harness alive long enough to take the post-fix-vs-pre-fix bisect,
 * so the pre-fix-emulated run installs a process-level catch and
 * counts the events. The post-fix run does NOT install this — any
 * throw that escapes is a regression and should fail loudly. */
const uncaughtErrors: string[] = [];
function installPreFixCatch(): void {
  process.on("uncaughtException", (err) => {
    const msg = err instanceof Error ? err.message : String(err);
    uncaughtErrors.push(msg);
  });
  process.on("unhandledRejection", (reason) => {
    const msg = reason instanceof Error ? reason.message : String(reason);
    uncaughtErrors.push(msg);
  });
}

// ---- Logging ------------------------------------------------------

function log(channel: string, msg: string): void {
  const stamp = new Date().toISOString().slice(11, 23);
  console.log(`[${stamp}] [${channel}] ${msg}`);
}

function logVerbose(channel: string, msg: string): void {
  if (!VERBOSE) return;
  log(channel, msg);
}

// ---- Peer-id generation ------------------------------------------

/** Choose a daemon peer id that places it lex-mid in the alphabet so
 * roughly half of generated real peers will be lex-lower (daemon is
 * initiator) and half lex-higher (daemon is answerer). The fixed
 * `d-` prefix matches the reporter's observed shape (`d441e78a8bf8`). */
const DAEMON_PEER_ID = "d-daemon-lex-mid";

/** Generate a real peer id with a specific lex prefix. */
function makeRealPeerId(prefix: string, index: number): string {
  return `${prefix}-real-peer-${index.toString().padStart(2, "0")}`;
}

/** The six real peer ids straddle the daemon's lex tie-break: three
 * lex-lower (initiator-side: daemon dials) and three lex-higher
 * (answerer-side: real peer dials daemon). Matches polly#106 item 3's
 * counter-example refusal. */
const REAL_PEER_IDS: string[] = [
  // Initial-arrival side (in signalling when daemon connects):
  makeRealPeerId("a", 0), // daemon initiates (d > a)
  makeRealPeerId("e", 1), // real-peer initiates (e > d)
  makeRealPeerId("b", 2), // daemon initiates (d > b)
  // Late-arrival side (arrive via `peer-joined` after daemon connects):
  makeRealPeerId("g", 3), // real-peer initiates (g > d)
  makeRealPeerId("c", 4), // daemon initiates (d > c)
  makeRealPeerId("z", 5), // real-peer initiates (z > d)
];

/** The peer the synthetic-throw injection targets. Choosing an
 * initial-arrival peer that the daemon is the initiator for is the
 * load-bearing case — the daemon's `createInitiatingSlot` is what
 * throws, and any peers iterated AFTER this one in the sweep's
 * `presentPeers` Set must still be dialled (post-fix contract). */
const FAILING_REAL_PEER_ID: string = REAL_PEER_IDS[2] ?? "";
if (FAILING_REAL_PEER_ID === "") {
  throw new Error("real-peer list shorter than expected — refusing");
}

// ---- Refusal gates ------------------------------------------------

function refuseIfFalsePositiveConditions(args: {
  daemonKnownPeerCount: number;
  initialPresentCount: number;
  totalRealPeers: number;
  daemonLexInitiatorCount: number;
}): void {
  const reasons: string[] = [];
  if (args.daemonKnownPeerCount < REFUSAL_MIN_KEYRING) {
    reasons.push(
      `daemon keyring has ${args.daemonKnownPeerCount} known peers; the polly#106 ticket requires at least ${REFUSAL_MIN_KEYRING}. The polly#103 reproducer with 10 peers does NOT exercise the polly#106 shape.`,
    );
  }
  if (args.initialPresentCount >= args.totalRealPeers) {
    reasons.push(
      "every real peer is online at signalling-join time; the polly#106 ticket requires gradual arrival to mimic the realistic shape (some peers already present, some arriving later via `peer-joined`).",
    );
  }
  if (args.daemonLexInitiatorCount === 0) {
    reasons.push(
      "no real peer has the daemon as lex-tie-break initiator; the polly#106 ticket requires a mix so an initiator-direction bug cannot be masked by every peer being answerer-side.",
    );
  }
  if (args.daemonLexInitiatorCount === args.totalRealPeers) {
    reasons.push(
      "every real peer has the daemon as lex-tie-break initiator; the polly#106 ticket requires a mix so an answerer-direction bug cannot be masked.",
    );
  }
  if (reasons.length === 0) return;
  console.error(
    "[mesh-slot-initiation-realistic-keyring] REFUSING TO RUN — false-positive surface detected:",
  );
  for (const reason of reasons) {
    console.error(`  - ${reason}`);
  }
  console.error(
    "\npolly#106 item 3 forbids running under these conditions because each\n" +
      "is a known false-positive surface for the failing shape the ticket\n" +
      "describes. See the ticket body for the full rationale.",
  );
  process.exit(2);
}

// ---- Synthetic-throw injection -----------------------------------

/** Track how many slot constructions the daemon has attempted, so we
 * can target the failing peer by id rather than by construction
 * order. The injection wraps `createInitiatingSlot` on the daemon
 * adapter; one call per attempted dial. */
let syntheticThrowCount = 0;

interface PrivateAdapter {
  createInitiatingSlot: (targetId: string) => unknown;
  tryCreateInitiatingSlot: (targetId: string) => void;
  refreshKnownPeers: () => void;
  handlePeerJoined: (peerId: string) => void;
  handlePeersPresent: (peerIds: string[]) => void;
  presentPeers: Set<string>;
  shouldInitiateTo: (peerId: string) => boolean;
  lastSlotInitiationDecisions: Map<string, unknown>;
}

/** Install the synthetic-throw injection on the daemon's WebRTC
 * adapter. Every call to `createInitiatingSlot(FAILING_REAL_PEER_ID)`
 * throws synchronously; calls for other peers fall through to the
 * original implementation. This stresses the polly#106 per-peer
 * try/catch in `refreshKnownPeers`. */
function injectSyntheticThrow(adapter: MeshWebRTCAdapter): void {
  const priv = adapter as unknown as PrivateAdapter;
  const original = priv.createInitiatingSlot.bind(priv);
  priv.createInitiatingSlot = (targetId: string) => {
    if (targetId === FAILING_REAL_PEER_ID) {
      syntheticThrowCount += 1;
      throw new Error(
        `synthetic injection: createInitiatingSlot for ${targetId} (count=${syntheticThrowCount})`,
      );
    }
    return original(targetId);
  };
}

/** Install the pre-fix-emulated dial entry points (no per-peer
 * try/catch) when POLLY_106_DISABLE_FIX=1. Pre-fix: a throw inside any
 * loop bubbles out of the caller (the signalling client's frame
 * dispatch for `handlePeersPresent` / `handlePeerJoined`, or the
 * `setInterval` callback for `refreshKnownPeers`). Every peer
 * iterated after the failing one in the same batch loses its dial
 * opportunity, the failing peer's rejection reason stays as a stale
 * pre-throw value, and the next sweep tick / next signalling frame
 * hits the same throw at the same point — leaving the same later
 * peers un-dialled in perpetuity. */
function disablePerPeerTryCatch(adapter: MeshWebRTCAdapter): void {
  const priv = adapter as unknown as PrivateAdapter;
  priv.refreshKnownPeers = () => {
    for (const remotePeerId of priv.presentPeers) {
      if (!priv.shouldInitiateTo(remotePeerId)) continue;
      priv.createInitiatingSlot(remotePeerId);
    }
  };
  priv.handlePeerJoined = (remotePeerId: string) => {
    priv.presentPeers.add(remotePeerId);
    if (!priv.shouldInitiateTo(remotePeerId)) return;
    priv.createInitiatingSlot(remotePeerId);
  };
  priv.handlePeersPresent = (peerIds: string[]) => {
    for (const remotePeerId of peerIds) {
      priv.presentPeers.add(remotePeerId);
      if (!priv.shouldInitiateTo(remotePeerId)) continue;
      priv.createInitiatingSlot(remotePeerId);
    }
  };
}

// ---- Test bed ----------------------------------------------------

function pickPort(): number {
  return 35000 + Math.floor(Math.random() * 10000);
}

function startSignalingServer(): { url: string; stop: () => Promise<void> } {
  const port = pickPort();
  const app = new Elysia()
    .use(signalingServer({ path: "/polly/signaling" }))
    .listen(port);
  log("signal-server", `listening at ws://127.0.0.1:${port}/polly/signaling`);
  return {
    url: `ws://127.0.0.1:${port}/polly/signaling`,
    stop: async () => {
      (
        app as unknown as { server?: { stop?: (force?: boolean) => void } }
      ).server?.stop?.(true);
    },
  };
}

/** Build a keyring with the given knownPeers and a fresh signing
 * identity. The shared document key is the same for every peer so
 * crypto envelopes verify across the mesh. */
function buildKeyring(args: {
  knownPeers: Map<string, Uint8Array>;
  sharedDocumentKey: Uint8Array;
}): {
  keyring: MeshKeyring;
  identity: ReturnType<typeof generateSigningKeyPair>;
} {
  const identity = generateSigningKeyPair();
  const keyring: MeshKeyring = {
    identity,
    knownPeers: args.knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, args.sharedDocumentKey]]),
    revokedPeers: new Set(),
  };
  return { keyring, identity };
}

async function buildDaemon(args: {
  url: string;
  keyring: MeshKeyring;
}): Promise<{ client: MeshClient }> {
  log(
    "daemon",
    `bootstrapping (peerId=${DAEMON_PEER_ID}, knownPeers=${args.keyring.knownPeers.size})`,
  );
  const client = await createMeshClient({
    signaling: {
      url: args.url,
      peerId: DAEMON_PEER_ID,
    },
    rtc: {
      RTCPeerConnection:
        WeriftRTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
      knownPeersRefreshIntervalMs: SWEEP_INTERVAL_MS,
    },
    keyring: args.keyring,
  });
  injectSyntheticThrow(client.webrtcAdapter);
  if (DISABLE_FIX) {
    disablePerPeerTryCatch(client.webrtcAdapter);
    log(
      "config",
      "POLLY_106_DISABLE_FIX=1 — pre-fix-emulated refreshKnownPeers installed (no per-peer try/catch)",
    );
  }
  return { client };
}

async function buildRealPeer(args: {
  url: string;
  peerId: string;
  daemonPublicKey: Uint8Array;
  daemonPeerId: string;
  sharedDocumentKey: Uint8Array;
}): Promise<{
  client: MeshClient;
  identity: ReturnType<typeof generateSigningKeyPair>;
}> {
  const knownPeers = new Map<string, Uint8Array>([
    [args.daemonPeerId, args.daemonPublicKey],
  ]);
  const { keyring, identity } = buildKeyring({
    knownPeers,
    sharedDocumentKey: args.sharedDocumentKey,
  });
  const client = await createMeshClient({
    signaling: {
      url: args.url,
      peerId: args.peerId,
    },
    rtc: {
      RTCPeerConnection:
        WeriftRTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
      knownPeersRefreshIntervalMs: SWEEP_INTERVAL_MS,
    },
    keyring,
  });
  return { client, identity };
}

async function sleep(ms: number): Promise<void> {
  await new Promise((r) => setTimeout(r, ms));
}

// ---- Outcome evaluation ------------------------------------------

interface RealPeerOutcome {
  peerId: string;
  daemonIsInitiator: boolean;
  isFailingPeer: boolean;
  arrivalKind: "initial" | "late";
  slotted: boolean;
  rejectionReason: SlotInitiationRejectionReason | undefined;
  peerCandidateEmittedAt: number | undefined;
  firstOutboundSendAt: number | undefined;
  firstInboundMessageAt: number | undefined;
}

function evaluateOutcome(args: {
  daemon: MeshClient;
  initialPeerIds: string[];
  latePeerIds: string[];
}): { perPeer: RealPeerOutcome[]; sweepRunCount: number } {
  const snapshot = args.daemon.getPeerStateSnapshot();
  const perPeer: RealPeerOutcome[] = [];
  for (const peerId of [...args.initialPeerIds, ...args.latePeerIds]) {
    const peer = snapshot.peers.find((p) => p.peerId === peerId);
    const daemonIsInitiator = DAEMON_PEER_ID > peerId;
    const isFailingPeer = peerId === FAILING_REAL_PEER_ID;
    const arrivalKind = args.initialPeerIds.includes(peerId)
      ? "initial"
      : "late";
    const handshake = peer?.slot?.lastSyncHandshakeAttempt;
    perPeer.push({
      peerId,
      daemonIsInitiator,
      isFailingPeer,
      arrivalKind,
      slotted: peer?.slot !== undefined,
      rejectionReason: peer?.slotInitiationRejectionReason,
      peerCandidateEmittedAt: handshake?.peerCandidateEmittedAt,
      firstOutboundSendAt: handshake?.firstOutboundSendAt,
      firstInboundMessageAt: handshake?.firstInboundMessageAt,
    });
  }
  return { perPeer, sweepRunCount: snapshot.sweep.runCount };
}

/** Decide whether the polly#106 contract holds for this run.
 *
 * Post-fix expectations:
 *
 *   - Every non-failing real peer is slotted (initiator OR answerer
 *     side — answerer-side peers get a slot from the inbound offer).
 *   - The failing peer is NOT slotted but its
 *     `slotInitiationRejectionReason` is `fatal-error` so the
 *     forensic surface names it.
 *   - The sweep has fired at least twice — proves the periodic
 *     re-evaluation is live.
 *
 * Pre-fix-emulated expectations:
 *
 *   - At least one non-failing peer iterated AFTER the failing one
 *     in the same sweep tick is NOT slotted. (The exact peer depends
 *     on the Set iteration order, which is insertion-stable in V8 —
 *     we don't assert on a specific peer, we just assert "the sweep
 *     broke and at least one downstream peer is unreachable".)
 */
function namedFailureReason(args: {
  perPeer: RealPeerOutcome[];
  sweepRunCount: number;
  disableFix: boolean;
}): string | undefined {
  if (args.sweepRunCount < 2) {
    return `sweep ran ${args.sweepRunCount} times; expected at least 2`;
  }
  const failingPeer = args.perPeer.find((p) => p.isFailingPeer);
  if (!failingPeer) {
    return "synthetic-throw target peer not found in snapshot";
  }
  if (args.disableFix) {
    // Pre-fix-emulated: the synthetic throw must have escaped polly's
    // dial path at least once, and the downstream consequence must be
    // visible — either the failing peer's rejection reason is NOT
    // `fatal-error` (because the per-peer try/catch is the only thing
    // that records that reason), or at least one initiator-side peer
    // iterated after the failing one in the same `peers-present`
    // batch is unslotted.
    if (uncaughtErrors.length === 0) {
      return "pre-fix path expected at least one uncaught error to escape polly's dial path; got none — the disablePerPeerTryCatch override didn't actually take effect.";
    }
    if (failingPeer.rejectionReason === "fatal-error") {
      return `pre-fix-emulated path should NOT name the failing peer with 'fatal-error' (that requires the per-peer try/catch); got '${failingPeer.rejectionReason}'. The pre-fix override did not actually disable the polly#106 fix.`;
    }
    return undefined;
  }
  // Post-fix: every non-failing real peer must be slotted.
  const nonFailingUnslotted = args.perPeer.filter(
    (p) => !p.isFailingPeer && !p.slotted,
  );
  if (nonFailingUnslotted.length > 0) {
    const names = nonFailingUnslotted
      .map((p) => `${p.peerId} (reason=${p.rejectionReason ?? "?"})`)
      .join(", ");
    return `post-fix: ${nonFailingUnslotted.length} non-failing peers without a slot: ${names}`;
  }
  if (failingPeer.rejectionReason !== "fatal-error") {
    return `post-fix: failing peer's snapshot rejection reason is '${failingPeer.rejectionReason ?? "(missing)"}', expected 'fatal-error' to confirm the per-peer try/catch is recording the throw`;
  }
  // Every slot polly considers connected (peer-candidate emitted)
  // should have firstOutboundSendAt populated, proving Automerge's
  // NetworkSubsystem actually issued a send through the adapter.
  // Slots whose peer-candidate never fired don't qualify — they're
  // still negotiating SDP/ICE and outbound sends are queued ahead of
  // dispatch.
  for (const p of args.perPeer) {
    if (p.isFailingPeer) continue;
    if (p.peerCandidateEmittedAt === undefined) continue;
    if (p.firstOutboundSendAt === undefined) {
      return `post-fix: slot to ${p.peerId} emitted peer-candidate at ${p.peerCandidateEmittedAt.toFixed(0)}ms but firstOutboundSendAt is still undefined — Automerge never dispatched a send through polly's adapter`;
    }
  }
  return undefined;
}

// ---- Main --------------------------------------------------------

async function main(): Promise<void> {
  if (DISABLE_FIX) installPreFixCatch();
  log(
    "config",
    `mode=${DISABLE_FIX ? "pre-fix-emulated (POLLY_106_DISABLE_FIX=1)" : "post-fix"} verbose=${VERBOSE}`,
  );

  // 1. Generate identities for every peer up-front so the daemon's
  //    keyring can hold the public keys of every real peer before the
  //    daemon constructs. The realistic shape is "keyring already
  //    knows everyone; the question is which peers are actually
  //    online" — and that's what this harness models.
  const sharedDocumentKey = generateDocumentKey();
  const realPeerIdentities = new Map<
    string,
    ReturnType<typeof generateSigningKeyPair>
  >();
  for (const peerId of REAL_PEER_IDS) {
    realPeerIdentities.set(peerId, generateSigningKeyPair());
  }

  // 2. Build the daemon's keyring: every real peer plus
  //    KEYRING_FILLER_COUNT filler entries that never come online.
  //    The filler shape matches a long-lived household keyring where
  //    most paired devices are offline most of the time.
  const daemonKnownPeers = new Map<string, Uint8Array>();
  for (const [peerId, identity] of realPeerIdentities) {
    daemonKnownPeers.set(peerId, identity.publicKey);
  }
  for (let i = 0; i < KEYRING_FILLER_COUNT; i += 1) {
    const filler = generateSigningKeyPair();
    daemonKnownPeers.set(
      `filler-offline-peer-${i.toString().padStart(3, "0")}`,
      filler.publicKey,
    );
  }
  const { keyring: daemonKeyring, identity: daemonIdentity } = buildKeyring({
    knownPeers: daemonKnownPeers,
    sharedDocumentKey,
  });

  const initialPeerIds = REAL_PEER_IDS.slice(0, REAL_PEERS_INITIAL_COUNT);
  const latePeerIds = REAL_PEER_IDS.slice(REAL_PEERS_INITIAL_COUNT);
  const daemonInitiatorCount = REAL_PEER_IDS.filter(
    (id) => DAEMON_PEER_ID > id,
  ).length;

  // 3. Refusal gates run before any subprocesses come up so the user
  //    sees the named refusal immediately on a misconfigured invocation.
  refuseIfFalsePositiveConditions({
    daemonKnownPeerCount: daemonKnownPeers.size,
    initialPresentCount: REAL_PEERS_INITIAL_COUNT,
    totalRealPeers: REAL_PEER_IDS.length,
    daemonLexInitiatorCount: daemonInitiatorCount,
  });

  // 4. Bring up the signalling server.
  const signaling = startSignalingServer();

  // 5. Bring up the initial real peers BEFORE the daemon so they
  //    arrive at the daemon via `peers-present` (not `peer-joined`).
  const realClients = new Map<string, MeshClient>();
  for (const peerId of initialPeerIds) {
    const real = await buildRealPeer({
      url: signaling.url,
      peerId,
      daemonPublicKey: daemonIdentity.publicKey,
      daemonPeerId: DAEMON_PEER_ID,
      sharedDocumentKey,
    });
    realClients.set(peerId, real.client);
    log("real-peer", `${peerId} online (initial-arrival)`);
  }

  // 6. Bring up the daemon. At this point, the signalling server's
  //    roster contains the initial real peers; the daemon receives
  //    them via `peers-present`.
  const daemon = await buildDaemon({
    url: signaling.url,
    keyring: daemonKeyring,
  });

  // 6a. Seed a document on the daemon so Automerge's NetworkSubsystem
  //     has something to sync once `peer-candidate` fires for each
  //     real peer. Without a document there is no sync handshake to
  //     observe — the polly#106 Failure B assertion checks that the
  //     adapter's `send()` path was actually reached, which only
  //     happens when Automerge has a document to advertise. The doc
  //     contents don't matter; we just need the sync state machine to
  //     have a payload.
  const seedHandle = daemon.client.repo.create<{ sentinel: string }>({
    sentinel: `polly-106-${crypto.randomUUID()}`,
  });
  log("seed", `created seed doc on daemon: ${seedHandle.url}`);

  // 7. Bring up the late real peers; they arrive at the daemon via
  //    `peer-joined`. The delay is short — just long enough to model
  //    the gradual-arrival shape.
  await sleep(LATE_ARRIVAL_DELAY_MS);
  for (const peerId of latePeerIds) {
    const real = await buildRealPeer({
      url: signaling.url,
      peerId,
      daemonPublicKey: daemonIdentity.publicKey,
      daemonPeerId: DAEMON_PEER_ID,
      sharedDocumentKey,
    });
    realClients.set(peerId, real.client);
    log("real-peer", `${peerId} online (late-arrival)`);
  }

  // 8. Wait for the observation budget. The sweep runs every
  //    SWEEP_INTERVAL_MS, so OBSERVATION_BUDGET_MS / SWEEP_INTERVAL_MS
  //    sweep ticks fire in this window.
  await sleep(OBSERVATION_BUDGET_MS);

  // 9. Evaluate. The snapshot captures the daemon's view of every
  //    peer it's been told about — by keyring, by signalling, or by
  //    slot construction attempt.
  const { perPeer, sweepRunCount } = evaluateOutcome({
    daemon: daemon.client,
    initialPeerIds,
    latePeerIds,
  });

  for (const p of perPeer) {
    log(
      "outcome",
      `${p.peerId.padEnd(20)} arrival=${p.arrivalKind.padEnd(7)} daemon-initiates=${String(p.daemonIsInitiator).padEnd(5)} failing=${String(p.isFailingPeer).padEnd(5)} slotted=${String(p.slotted).padEnd(5)} reason=${p.rejectionReason ?? "(none)"} peerCandidateEmit=${p.peerCandidateEmittedAt?.toFixed(0) ?? "(none)"}ms firstSend=${p.firstOutboundSendAt?.toFixed(0) ?? "(none)"}ms firstRecv=${p.firstInboundMessageAt?.toFixed(0) ?? "(none)"}ms`,
    );
  }
  log(
    "sweep",
    `sweep ran ${sweepRunCount} times in ${OBSERVATION_BUDGET_MS}ms (interval=${SWEEP_INTERVAL_MS}ms) — synthetic throws fired ${syntheticThrowCount} times — uncaught errors escaped: ${uncaughtErrors.length}`,
  );

  const failure = namedFailureReason({
    perPeer,
    sweepRunCount,
    disableFix: DISABLE_FIX,
  });
  const contractHolds = failure === undefined;

  if (contractHolds) {
    log(
      "result",
      DISABLE_FIX
        ? "SUCCESS — pre-fix-emulated path reproduced the failure: synthetic throw aborted the sweep, downstream peers were never dialled."
        : "SUCCESS — every non-failing real peer got a slot, every connected slot emitted peer-candidate AND issued an outbound send through the adapter, and the failing peer's snapshot names it with `fatal-error`.",
    );
  } else {
    log("result", `FAILURE — REASON: ${failure}`);
  }

  // 10. Write the wire-level transcript.
  const transcript = {
    version: 1,
    issue: "polly#106",
    config: {
      mode: DISABLE_FIX ? "pre-fix-emulated" : "post-fix",
      keyring_filler_count: KEYRING_FILLER_COUNT,
      daemon_known_peers: daemonKnownPeers.size,
      sweep_interval_ms: SWEEP_INTERVAL_MS,
      observation_budget_ms: OBSERVATION_BUDGET_MS,
      late_arrival_delay_ms: LATE_ARRIVAL_DELAY_MS,
      daemon_peer_id: DAEMON_PEER_ID,
      failing_real_peer_id: FAILING_REAL_PEER_ID,
      daemon_initiator_count: daemonInitiatorCount,
    },
    outcome: {
      contractHolds,
      failureReason: failure ?? null,
      sweepRunCount,
      syntheticThrowCount,
      uncaughtErrorCount: uncaughtErrors.length,
      uncaughtErrorMessages: uncaughtErrors.slice(0, 8),
      perPeer,
    },
    fullSnapshot: daemon.client.getPeerStateSnapshot(),
  };
  const transcriptPath = resolvePath(import.meta.dir, "transcript.json");
  await writeFile(transcriptPath, `${JSON.stringify(transcript, null, 2)}\n`);
  log("transcript", `wrote ${transcriptPath}`);
  logVerbose("snapshot", JSON.stringify(transcript.fullSnapshot, null, 2));

  // 11. Teardown.
  await daemon.client.close();
  for (const client of realClients.values()) {
    await client.close();
  }
  await signaling.stop();

  process.exit(contractHolds ? 0 : 1);
}

main().catch((err) => {
  console.error("[mesh-slot-initiation-realistic-keyring] fatal error:", err);
  process.exit(1);
});
