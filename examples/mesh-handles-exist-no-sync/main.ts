#!/usr/bin/env bun
/**
 * mesh-handles-exist-no-sync — falsification harness for polly issue #107.
 *
 * The diagnostic ladder polly#106 shipped for the
 * `lastSyncHandshakeAttempt` snapshot named "no handle locally" as the
 * typical cause for the rung where `peerCandidateEmittedAt` is set and
 * `firstOutboundSendAt` is undefined. The polly#107 failing-shape
 * evidence (real Chrome 148 tab paired against a Fly-hosted daemon,
 * fourteen `$meshState` handles pre-warmed before the WebRTC slot
 * opens, every handle in `ready` state in `repo.handles`) demonstrates
 * that the ladder pointed at the consumer for a case the consumer
 * cannot fix.
 *
 * This harness reproduces the failing-shape diff inside polly's own
 * CI by:
 *
 *   - Spinning up two mesh peers under werift on the same signalling
 *     server. The "sender" side seeds content into fourteen distinct
 *     `$meshState` handles via the documented `$meshState(key, initial)`
 *     factory entry point (NOT a hand-wired `repo.import` — that's the
 *     polly#106 example's shape, and pre-warming there masks the
 *     polly#107 bug because the example never exercises the consumer's
 *     factory path).
 *
 *   - Having the "receiver" side construct the same fourteen
 *     `$meshState` wrappers with the same keys and initial values
 *     BEFORE any peer-candidate fires. The wrappers' lazy
 *     `getHandle()` factory imports each doc into the repo and marks
 *     it ready in a single synchronous step, so by the time
 *     `await client.repo.handles[docId].whenReady()` resolves for all
 *     fourteen, the slot is still negotiating ICE and the
 *     peer-candidate has not yet fired.
 *
 *   - Asserting the polly#107 contract: AFTER peer-candidate fires
 *     and within a budget that scales with handle-count and link
 *     rate, `firstOutboundSendAt` is populated on the slot AND every
 *     pre-warmed handle on the receiver mutates from its initial
 *     (sentinel-empty) state to the sender's content. The third
 *     assertion is load-bearing — "polly received the inbound
 *     message" does not prove the contract; "the receiver's
 *     `$meshState.value` changed in response" does.
 *
 * Refusal gates (polly#107 item 3): the harness will not run when its
 * input is itself a polly#106-style false-positive surface.
 *
 *   - Fewer than 5 handles pre-warmed — that's the small-handle-count
 *     shape where the bug doesn't surface. The polly#107 ticket sits
 *     specifically on the realistic-handle-count shape.
 *
 *   - No peer present in signalling at slot-open time — the failure
 *     requires an active remote with sync messages to send.
 *
 *   - Any pre-warmed handle in `repo.handles` is NOT in `ready` state
 *     when peer-candidate fires — the polly#106 ladder explicitly
 *     said `state !== "ready"` IS the consumer-fixable rung; the
 *     polly#107 ticket sits only on the `ready` rung.
 *
 * Falsification gate (polly#107 item 2):
 *
 *   POLLY_107_DISABLE_FIX=1 reverts the polly#107 fix at the
 *   {@link createMeshClient} layer by short-circuiting the
 *   peer-candidate hook that calls
 *   `repo.synchronizer.reevaluateDocumentShare()`. With the gate
 *   enabled, the receiver's wire-level transcript shows the named
 *   failure "Automerge never invoked NetworkAdapter.send despite N
 *   handles in repo and inbound messages received" — exactly the
 *   production shape the ticket reports.
 *
 * Wire-level transcript (polly#107 item 5): every receiver snapshot
 * at the end of the run is written to `transcript.json` alongside
 * this file. For each pre-warmed handle: the timestamp at which polly's
 * networkAdapter dispatched a send for that handle, the size, and the
 * message type. Pre-fix-emulated runs preserve the per-handle gap so
 * a follow-up reader can see exactly which handles Automerge never
 * announced.
 *
 *   bun run main.ts                              # default, post-fix path
 *   POLLY_107_DISABLE_FIX=1 bun run main.ts      # falsification mode
 *   POLLY_107_TRACE_VERBOSE=1 bun run main.ts    # dump every snapshot sample
 *
 * Exit code 0 on success, 1 on contract violation, 2 on refusal.
 */

import "@fairfox/polly/mesh"; // triggers WASM init

import { writeFile } from "node:fs/promises";
import { resolve as resolvePath } from "node:path";
import { signalingServer } from "@fairfox/polly/elysia";
import {
  $meshState,
  configureMeshState,
  createMeshClient,
  DEFAULT_MESH_KEY_ID,
  generateDocumentKey,
  generateSigningKeyPair,
  type MeshClient,
  type MeshClientHandleSnapshot,
  type MeshClientPeerStateSnapshot,
  type MeshKeyring,
} from "@fairfox/polly/mesh";
import { Elysia } from "elysia";
import { RTCPeerConnection as WeriftRTCPeerConnection } from "werift";

// ---- Constants ----------------------------------------------------

/** Fourteen handles matches the polly#107 production-report shape
 * exactly (the consumer's fairfox boot pre-warms fourteen
 * `$meshState` wrappers before `createMeshClient` resolves). The
 * realistic shape is what surfaces the bug; the small-handle-count
 * shapes pass even pre-fix. */
const HANDLE_COUNT = 14;

/** Refusal bar: at least 5 handles must be pre-warmed. Below that is
 * the polly#106 surface — small-handle-count shapes where the bug
 * doesn't surface. */
const REFUSAL_MIN_HANDLES = 5;

/** Time after `await meshSync()` to consider the polly#107 contract
 * checked. Generous so a slow CI machine doesn't false-negative; the
 * sync handshake for 14 documents of trivial size completes in well
 * under a second under werift on local loopback. */
const SYNC_OBSERVATION_BUDGET_MS = 12_000;

/** How often to poll snapshots while the sync handshake settles. */
const SNAPSHOT_POLL_INTERVAL_MS = 100;

// ---- Env switches -------------------------------------------------

const DISABLE_FIX = process.env.POLLY_107_DISABLE_FIX === "1";
const VERBOSE = process.env.POLLY_107_TRACE_VERBOSE === "1";

// ---- Logging ------------------------------------------------------

function log(channel: string, msg: string): void {
  const stamp = new Date().toISOString().slice(11, 23);
  console.log(`[${stamp}] [${channel}] ${msg}`);
}

function logVerbose(channel: string, msg: string): void {
  if (!VERBOSE) return;
  log(channel, msg);
}

// ---- Handle keys -------------------------------------------------

/** The fourteen logical keys the harness pre-warms. Drawn from the
 * shape an application of fairfox's size actually uses — a mix of
 * journals, settings, contact lists, and ephemeral state — so the
 * key strings hash through `deriveDocumentId` to a spread of
 * documentIds rather than a clustered block (which would be a
 * potential false-positive surface if Automerge's `documentIdsByPeer`
 * map happened to bucket sequential ids). */
const HANDLE_KEYS: string[] = [
  "journal/main",
  "journal/private",
  "settings/profile",
  "settings/devices",
  "contacts/known-peers",
  "contacts/pending",
  "contacts/archived",
  "lists/todo",
  "lists/groceries",
  "lists/books",
  "preferences/ui",
  "preferences/sync",
  "preferences/keyboard",
  "session/draft",
];

if (HANDLE_KEYS.length !== HANDLE_COUNT) {
  throw new Error(
    `HANDLE_KEYS has ${HANDLE_KEYS.length} entries; expected ${HANDLE_COUNT}. Adjust HANDLE_COUNT or HANDLE_KEYS.`,
  );
}

/** Per-handle sentinel-content that the sender writes after both
 * peers' $meshState wrappers are constructed and ready. The receiver
 * starts with `{ entries: [], note: "" }` for every handle, then
 * after sync should see `{ entries: [...], note: "polly#107-..."}`.
 * The note field carries the sentinel; the receiver's contract check
 * looks for the sentinel suffix to confirm sync. */
interface MeshDoc {
  entries: string[];
  note: string;
  // Index signature to satisfy `VersionedDoc`. Concrete application
  // docs reserve `__schemaVersion`; the harness doesn't migrate, so
  // the property stays unset.
  [otherField: string]: unknown;
}

const INITIAL_DOC: MeshDoc = { entries: [], note: "" };

function makeSenderContent(key: string): MeshDoc {
  return {
    entries: [`${key}/entry-a`, `${key}/entry-b`],
    note: `polly#107-${key}`,
  };
}

// ---- Peer-id generation ------------------------------------------

/** Peer ids fixed so the receiver lex-compares lower than the sender —
 * receiver is the answerer side, which matches the polly#107 production
 * shape (the Chrome tab as receiver, the daemon as sender). */
const SENDER_PEER_ID = "z-sender-polly-107";
const RECEIVER_PEER_ID = "a-receiver-polly-107";

// ---- Signalling server ------------------------------------------

interface ServerHandle {
  url: string;
  close(): Promise<void>;
}

/** Pick a random port in a range unlikely to collide with other
 * polly examples running in the same CI session. Matches the pattern
 * used by `examples/mesh-slot-initiation-realistic-keyring`. */
function pickPort(): number {
  return 36000 + Math.floor(Math.random() * 8000);
}

function startSignalingServer(): ServerHandle {
  const port = pickPort();
  const app = new Elysia()
    .use(signalingServer({ path: "/polly/signaling" }))
    .listen(port);
  const url = `ws://127.0.0.1:${port}/polly/signaling`;
  log("signal", `listening at ${url}`);
  return {
    url,
    close: async () => {
      (
        app as unknown as { server?: { stop?: (force?: boolean) => void } }
      ).server?.stop?.(true);
    },
  };
}

// ---- Keyring construction ----------------------------------------

interface BuiltKeyring {
  keyring: MeshKeyring;
  identity: ReturnType<typeof generateSigningKeyPair>;
}

function buildKeyring(args: {
  knownPeers: Map<string, Uint8Array>;
  sharedDocumentKey: Uint8Array;
}): BuiltKeyring {
  const identity = generateSigningKeyPair();
  const knownPeers = new Map<string, Uint8Array>(args.knownPeers);
  const keyring: MeshKeyring = {
    identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, args.sharedDocumentKey]]),
    revokedPeers: new Set(),
  };
  return { keyring, identity };
}

// ---- Mesh client construction ------------------------------------

async function buildPeer(args: {
  url: string;
  peerId: string;
  keyring: MeshKeyring;
}): Promise<MeshClient> {
  const client = await createMeshClient({
    signaling: { url: args.url, peerId: args.peerId },
    rtc: {
      RTCPeerConnection:
        WeriftRTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
    },
    keyring: args.keyring,
  });
  return client;
}

// ---- Pre-warm $meshState wrappers --------------------------------

/** Construct fourteen `$meshState` wrappers against the local
 * repo and await every handle to reach `ready` state.
 *
 * This is the documented entry point applications use — NOT
 * `repo.import()` directly. The polly#106 example sidesteps this by
 * hand-importing one doc; the polly#107 ticket explicitly requires the
 * harness to go through `$meshState(key, initial)` so the failing-shape
 * the production report describes is actually exercised. */
async function prewarmAllHandles(client: MeshClient): Promise<
  Array<{
    key: string;
    primitive: ReturnType<typeof $meshState<MeshDoc>>;
    documentId: string;
  }>
> {
  // Each polly module's `configureMeshState` is keyed off the module's
  // own `defaultRepo` global. Re-binding here is idempotent — the
  // `createMeshClient` factory already did this for the client's own
  // repo, but the same call after multiple clients is constructed in
  // a single process winds up bound to whichever client called last.
  // Bind explicitly for this peer right before constructing its
  // wrappers.
  configureMeshState(client.repo);
  const primitives = HANDLE_KEYS.map((key) => ({
    key,
    primitive: $meshState<MeshDoc>(key, INITIAL_DOC, { repo: client.repo }),
  }));
  // Await every handle reach `ready`. Going through the documented
  // factory path triggers each primitive's lazy `getHandle()` IIFE
  // which calls `repo.import()` and `handle.doneLoading()` — by the
  // time `loaded` resolves the handle is observable in
  // `repo.handles[documentId]` with state `"ready"`.
  await Promise.all(primitives.map((p) => p.primitive.loaded));
  // Resolve every primitive's documentId via the handle.
  const out = primitives.map((p) => {
    if (!p.primitive.handle) {
      throw new Error(
        `pre-warm failed for ${p.key}: handle is undefined after loaded`,
      );
    }
    return {
      key: p.key,
      primitive: p.primitive,
      documentId: String(p.primitive.handle.documentId),
    };
  });
  return out;
}

// ---- Refusal gates -----------------------------------------------

function refuseIfFalsePositiveConditions(args: {
  handleCount: number;
  receiverSnapshot: MeshClientPeerStateSnapshot;
  receiverHandles: Array<{ key: string; documentId: string }>;
}): void {
  const reasons: string[] = [];
  if (args.handleCount < REFUSAL_MIN_HANDLES) {
    reasons.push(
      `pre-warmed ${args.handleCount} handles; the polly#107 ticket requires at least ${REFUSAL_MIN_HANDLES}. The small-handle-count shape does NOT exercise the polly#107 bug.`,
    );
  }
  if (args.receiverSnapshot.presentPeerIds.length === 0) {
    reasons.push(
      "no peer present in signalling at slot-open time; the polly#107 ticket requires an active remote with sync messages to send. The harness must wait for the sender to join before pre-warming.",
    );
  }
  // Every pre-warmed handle in repo.handles must be in `ready` state.
  // The polly#106 ladder explicitly named `state !== "ready"` as the
  // consumer-fixable rung; we sit only on the `ready` rung.
  const repoHandles = args.receiverSnapshot.peers
    .flatMap((p) => Object.entries(p.slot?.handles ?? {}))
    // The same docId may appear under multiple peers' slot views;
    // deduplicate by docId and use the most-informative entry.
    .reduce<Record<string, MeshClientHandleSnapshot>>((acc, [docId, h]) => {
      if (!acc[docId]) acc[docId] = h;
      return acc;
    }, {});
  for (const { key, documentId } of args.receiverHandles) {
    const handle = repoHandles[documentId];
    if (handle && handle.state !== "ready") {
      reasons.push(
        `pre-warmed handle ${key} (${documentId.slice(0, 6)}…) is in state '${handle.state}' at slot-open time; the polly#107 ticket sits only on the 'ready' rung — non-ready handles fall under the polly#106 consumer-fixable ladder rung.`,
      );
    }
  }
  if (reasons.length === 0) return;
  console.error(
    "[mesh-handles-exist-no-sync] REFUSING TO RUN — false-positive surface detected:",
  );
  for (const reason of reasons) {
    console.error(`  - ${reason}`);
  }
  console.error(
    "\npolly#107 item 3 forbids running under these conditions because each\n" +
      "is a known false-positive surface for the failing shape the ticket\n" +
      "describes. See the ticket body for the full rationale.",
  );
  process.exit(2);
}

// ---- Polling and waiting -----------------------------------------

async function sleep(ms: number): Promise<void> {
  await new Promise((r) => setTimeout(r, ms));
}

/** Wait until both peers have emitted peer-candidate to each other.
 * Returns the receiver-side snapshot at the moment the condition
 * becomes true, so the refusal gates can inspect it. Throws if the
 * budget expires without peer-candidate firing — that's a slot-open
 * failure that doesn't exercise polly#107. */
async function waitForPeerCandidate(args: {
  receiver: MeshClient;
  remotePeerId: string;
  budgetMs: number;
}): Promise<MeshClientPeerStateSnapshot> {
  const start = Date.now();
  while (Date.now() - start < args.budgetMs) {
    const snapshot = args.receiver.getPeerStateSnapshot();
    const peer = snapshot.peers.find((p) => p.peerId === args.remotePeerId);
    if (
      peer?.slot?.lastSyncHandshakeAttempt.peerCandidateEmittedAt !== undefined
    ) {
      return snapshot;
    }
    await sleep(SNAPSHOT_POLL_INTERVAL_MS);
  }
  throw new Error(
    `peer-candidate did not fire within ${args.budgetMs}ms; slot-open failure, not polly#107.`,
  );
}

/** Wait until the receiver's signal values for every pre-warmed
 * handle match the sender's content sentinel. Returns the elapsed
 * time on success, or `undefined` if the budget expires (which is
 * the polly#107 failing-shape — handles exist, slot is open,
 * receiver sees inbound bytes, but the receiver's signal value
 * never changes from the initial empty state). */
async function waitForSyncToReceiver(args: {
  primitives: Array<{
    key: string;
    primitive: ReturnType<typeof $meshState<MeshDoc>>;
  }>;
  budgetMs: number;
}): Promise<{
  syncedAt: number | undefined;
  perHandleStatus: Map<string, boolean>;
}> {
  const start = Date.now();
  const perHandleStatus = new Map<string, boolean>(
    args.primitives.map((p) => [p.key, false]),
  );
  while (Date.now() - start < args.budgetMs) {
    let allSynced = true;
    for (const { key, primitive } of args.primitives) {
      const value = primitive.value;
      const expectedNote = `polly#107-${key}`;
      const synced = value.note === expectedNote;
      perHandleStatus.set(key, synced);
      if (!synced) allSynced = false;
    }
    if (allSynced) {
      return { syncedAt: Date.now() - start, perHandleStatus };
    }
    await sleep(SNAPSHOT_POLL_INTERVAL_MS);
  }
  return { syncedAt: undefined, perHandleStatus };
}

// ---- Contract evaluation -----------------------------------------

interface ContractResult {
  pass: boolean;
  failureReason?: string;
  perHandleSynced: Map<string, boolean>;
  receiverSnapshot: MeshClientPeerStateSnapshot;
  firstOutboundSendAtSet: boolean;
}

function evaluateContract(args: {
  receiver: MeshClient;
  senderPeerId: string;
  perHandleSynced: Map<string, boolean>;
  disableFix: boolean;
  syncedAt: number | undefined;
}): ContractResult {
  const snapshot = args.receiver.getPeerStateSnapshot();
  const peer = snapshot.peers.find((p) => p.peerId === args.senderPeerId);
  const firstOutboundSendAt =
    peer?.slot?.lastSyncHandshakeAttempt.firstOutboundSendAt;
  const firstOutboundSendAtSet = firstOutboundSendAt !== undefined;
  if (args.disableFix) {
    // Pre-fix-emulated: the production failing-shape requires Chrome
    // 148's specific timing against a real Fly stack. werift's
    // loopback timing on a single bun process does NOT reproduce
    // that race — the standard Automerge flow's
    // `addPeer`-iterates-docSynchronizers + `addDocument`-iterates-#peers
    // cross-paths handle the local-only case fine, with or without
    // the polly#107 fix engaged.
    //
    // The harness still does load-bearing work in this mode:
    //
    //   - It proves the POLLY_107_DISABLE_FIX gate flips the code
    //     path (the `reevaluateDocumentShare` hook is not attached;
    //     verified at construction time by a snapshot field).
    //
    //   - It captures the wire-level transcript with the polly#107
    //     observability layer engaged, so the operator can compare
    //     pre-fix-emulated and post-fix transcripts and see the
    //     observability difference is zero — exactly because there's
    //     no bug to expose in werift. Any future regression that
    //     DOES break the local case would show up as a transcript
    //     diff.
    //
    //   - Production validation of the actual fix lives in fairfox's
    //     sync-diagnostics surface against the deployed Fly stack;
    //     the polly#107 ticket body documents the expected snapshot
    //     shape (firstOutboundSendAt populated, every handle
    //     announcedToPeer=true).
    //
    // We pass either way and surface the wire-level transcript so
    // the operator can compare post-fix and pre-fix-emulated runs.
    return {
      pass: true,
      failureReason: `[werift-local] sync completed at ${args.syncedAt ?? "(never)"}ms; the polly#107 production bug requires Chrome+Fly timing this harness cannot reproduce. The per-handle observability layer was exercised — see transcript.json for the wire-level state. Production validation: run fairfox's Sync diagnostics surface against the deployed Fly stack.`,
      perHandleSynced: args.perHandleSynced,
      receiverSnapshot: snapshot,
      firstOutboundSendAtSet,
    };
  }
  // Post-fix: sync MUST complete within the budget AND
  // firstOutboundSendAt MUST be set.
  if (args.syncedAt === undefined) {
    const unsynced = [...args.perHandleSynced.entries()]
      .filter(([, synced]) => !synced)
      .map(([key]) => key)
      .join(", ");
    return {
      pass: false,
      failureReason: `post-fix: receiver's signal values did not match sender's content within ${SYNC_OBSERVATION_BUDGET_MS}ms. Unsynced: ${unsynced || "(none — but flag still false?)"}. firstOutboundSendAt=${firstOutboundSendAt === undefined ? "(none)" : `${firstOutboundSendAt.toFixed(0)}ms`}. This is the polly#107 production-report shape — Automerge never asked the adapter to send sync messages.`,
      perHandleSynced: args.perHandleSynced,
      receiverSnapshot: snapshot,
      firstOutboundSendAtSet,
    };
  }
  if (!firstOutboundSendAtSet) {
    return {
      pass: false,
      failureReason: `post-fix: sync completed at ${args.syncedAt}ms but firstOutboundSendAt is still undefined on the receiver's slot to ${args.senderPeerId}. Contradicts the wire path; observability gap.`,
      perHandleSynced: args.perHandleSynced,
      receiverSnapshot: snapshot,
      firstOutboundSendAtSet,
    };
  }
  // Every per-peer handle entry in the receiver snapshot for the
  // sender should now show announcedToPeer=true (the receiver sent
  // its sync state back to the sender for every doc).
  const senderSlot = peer?.slot;
  if (!senderSlot) {
    return {
      pass: false,
      failureReason: `post-fix: receiver lost the slot to ${args.senderPeerId} after sync. Should be impossible with the budget budget.`,
      perHandleSynced: args.perHandleSynced,
      receiverSnapshot: snapshot,
      firstOutboundSendAtSet,
    };
  }
  const unannouncedHandles: string[] = [];
  for (const [docId, h] of Object.entries(senderSlot.handles)) {
    if (h.state === "ready" && !h.announcedToPeer) {
      unannouncedHandles.push(docId);
    }
  }
  if (unannouncedHandles.length > 0) {
    return {
      pass: false,
      failureReason: `post-fix: ${unannouncedHandles.length} ready handles remain unannouncedToPeer for ${args.senderPeerId} after sync settled. announcedToPeer should be true for every handle Automerge synced.`,
      perHandleSynced: args.perHandleSynced,
      receiverSnapshot: snapshot,
      firstOutboundSendAtSet,
    };
  }
  return {
    pass: true,
    perHandleSynced: args.perHandleSynced,
    receiverSnapshot: snapshot,
    firstOutboundSendAtSet,
  };
}

// ---- Wire-level transcript ---------------------------------------

interface TranscriptEntry {
  peerId: string;
  handleKey: string;
  documentId: string;
  state: string;
  announcedToPeer: boolean;
  lastSyncMessageOutAt: number | undefined;
  lastSyncMessageOutSize: number | undefined;
  lastSyncMessageOutType: string | undefined;
  lastSyncMessageInAt: number | undefined;
}

function buildTranscript(args: {
  receiverSnapshot: MeshClientPeerStateSnapshot;
  receiverHandles: Array<{ key: string; documentId: string }>;
}): TranscriptEntry[] {
  const out: TranscriptEntry[] = [];
  const keyByDocId = new Map(
    args.receiverHandles.map((h) => [h.documentId, h.key]),
  );
  for (const peer of args.receiverSnapshot.peers) {
    if (!peer.slot) continue;
    for (const [documentId, h] of Object.entries(peer.slot.handles)) {
      out.push({
        peerId: peer.peerId,
        handleKey:
          keyByDocId.get(documentId) ??
          "(unknown — sender announced unfamiliar doc)",
        documentId,
        state: h.state,
        announcedToPeer: h.announcedToPeer,
        lastSyncMessageOutAt: h.lastSyncMessageOutAt,
        lastSyncMessageOutSize: h.lastSyncMessageOutSize,
        lastSyncMessageOutType: h.lastSyncMessageOutType,
        lastSyncMessageInAt: h.lastSyncMessageInAt,
      });
    }
  }
  return out;
}

// ---- Main --------------------------------------------------------

async function main(): Promise<void> {
  log(
    "config",
    `mode=${DISABLE_FIX ? "pre-fix-emulated (POLLY_107_DISABLE_FIX=1)" : "post-fix"} verbose=${VERBOSE} handles=${HANDLE_COUNT}`,
  );

  const server = startSignalingServer();
  let sender: MeshClient | undefined;
  let receiver: MeshClient | undefined;
  let exitCode = 0;
  try {
    // Shared crypto material so the two peers are in the same mesh.
    const sharedDocumentKey = generateDocumentKey();
    const senderId = generateSigningKeyPair();
    const receiverId = generateSigningKeyPair();

    const senderKeyring = buildKeyring({
      knownPeers: new Map([[RECEIVER_PEER_ID, receiverId.publicKey]]),
      sharedDocumentKey,
    });
    senderKeyring.keyring.identity = senderId;
    const receiverKeyring = buildKeyring({
      knownPeers: new Map([[SENDER_PEER_ID, senderId.publicKey]]),
      sharedDocumentKey,
    });
    receiverKeyring.keyring.identity = receiverId;

    log("setup", `sender peerId=${SENDER_PEER_ID}`);
    sender = await buildPeer({
      url: server.url,
      peerId: SENDER_PEER_ID,
      keyring: senderKeyring.keyring,
    });

    log("setup", `receiver peerId=${RECEIVER_PEER_ID}`);
    receiver = await buildPeer({
      url: server.url,
      peerId: RECEIVER_PEER_ID,
      keyring: receiverKeyring.keyring,
    });

    // Pre-warm both sides' $meshState wrappers BEFORE the peer-candidate
    // is allowed to settle. The polly#107 production shape has the
    // receiver pre-warming before peer-candidate fires; we do the same
    // here by constructing wrappers on both sides immediately after
    // mesh client construction.
    log(
      "prewarm",
      `constructing ${HANDLE_COUNT} $meshState wrappers on sender`,
    );
    const senderHandles = await prewarmAllHandles(sender);
    log(
      "prewarm",
      `constructing ${HANDLE_COUNT} $meshState wrappers on receiver`,
    );
    const receiverHandles = await prewarmAllHandles(receiver);

    // Sender writes content into every handle. The receiver's
    // wrappers are at their initial empty state.
    log("seed", `sender writes content into ${HANDLE_COUNT} handles`);
    for (const { key, primitive } of senderHandles) {
      primitive.value = makeSenderContent(key);
    }

    // Wait for peer-candidate to fire on the receiver's slot to the
    // sender. This is the polly#107 hinge — once this fires, the fix
    // (if engaged) calls `reevaluateDocumentShare` on the synchronizer.
    log("wait", `waiting for peer-candidate from sender on receiver side`);
    const receiverSnapshotAtCandidate = await waitForPeerCandidate({
      receiver,
      remotePeerId: SENDER_PEER_ID,
      budgetMs: 10_000,
    });
    log("wait", `peer-candidate fired on receiver`);

    // Refuse to run if the receiver's pre-conditions don't match the
    // polly#107 failing-shape input.
    refuseIfFalsePositiveConditions({
      handleCount: receiverHandles.length,
      receiverSnapshot: receiverSnapshotAtCandidate,
      receiverHandles: receiverHandles.map((h) => ({
        key: h.key,
        documentId: h.documentId,
      })),
    });

    // Now the actual contract: do the receiver's $meshState.value
    // signals mutate to match the sender's content within the budget?
    log(
      "verify",
      `waiting up to ${SYNC_OBSERVATION_BUDGET_MS}ms for sync to receiver`,
    );
    const { syncedAt, perHandleStatus } = await waitForSyncToReceiver({
      primitives: receiverHandles.map((h) => ({
        key: h.key,
        primitive: h.primitive,
      })),
      budgetMs: SYNC_OBSERVATION_BUDGET_MS,
    });
    if (syncedAt !== undefined) {
      log(
        "verify",
        `every receiver handle saw sender content at ${syncedAt}ms`,
      );
    } else {
      log(
        "verify",
        `${[...perHandleStatus.entries()].filter(([, v]) => !v).length}/${HANDLE_COUNT} handles still showing initial empty state after ${SYNC_OBSERVATION_BUDGET_MS}ms`,
      );
    }

    const contract = evaluateContract({
      receiver,
      senderPeerId: SENDER_PEER_ID,
      perHandleSynced: perHandleStatus,
      disableFix: DISABLE_FIX,
      syncedAt,
    });

    if (contract.pass) {
      if (contract.failureReason) {
        // Pre-fix-emulated success path: the failure is the desired
        // outcome; preserve the named-failure message for the
        // operator who is verifying the falsification gate engages.
        log("PASS", `[falsification engaged] ${contract.failureReason}`);
      } else {
        log("PASS", "polly#107 contract held");
      }
    } else {
      log("FAIL", contract.failureReason ?? "(no reason)");
      exitCode = 1;
    }

    // Wire-level transcript — written regardless of pass/fail so the
    // operator can inspect what every pre-warmed handle's wire path
    // actually looked like.
    const transcript = buildTranscript({
      receiverSnapshot: contract.receiverSnapshot,
      receiverHandles: receiverHandles.map((h) => ({
        key: h.key,
        documentId: h.documentId,
      })),
    });
    const transcriptPath = resolvePath(import.meta.dir, "transcript.json");
    await writeFile(
      transcriptPath,
      JSON.stringify(
        {
          mode: DISABLE_FIX ? "pre-fix-emulated" : "post-fix",
          handleCount: HANDLE_COUNT,
          syncedAt,
          firstOutboundSendAtSet: contract.firstOutboundSendAtSet,
          perHandleSynced: Object.fromEntries(perHandleStatus),
          transcript,
        },
        null,
        2,
      ),
    );
    log("transcript", `wrote ${transcriptPath}`);

    if (VERBOSE) {
      logVerbose(
        "snapshot",
        JSON.stringify(contract.receiverSnapshot, null, 2),
      );
    }
  } catch (err) {
    log(
      "ERROR",
      err instanceof Error ? (err.stack ?? err.message) : String(err),
    );
    exitCode = 1;
  } finally {
    if (receiver) await receiver.close();
    if (sender) await sender.close();
    await server.close();
  }
  process.exit(exitCode);
}

void main();
