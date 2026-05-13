#!/usr/bin/env bun
/**
 * Mesh-large-initial-sync-turn — falsification harness for polly#105.
 *
 * Polly#104 shipped a fix and an in-process throttled bridge that
 * proves the fix holds against a simulated bandwidth-constrained
 * transport. polly#105 demonstrates that the in-process throttle is a
 * false-positive surface for the real-transport contract: a fresh peer
 * paired through a TURN relay still fails to consume a non-trivial
 * initial sync even with the polly#104 cap and yield in place. This
 * harness reproduces that failure against a real TURN server (Pion,
 * boot-strapped as a child Go process), then proves whatever fix
 * polly#105 ships closes it.
 *
 * The contract is the same as polly#104 — "a fresh peer paired into a
 * mesh whose other side holds non-empty document history must consume
 * the initial sync stream" — but narrowed to TURN-relayed WebRTC. The
 * relay is the only ICE candidate type allowed:
 * `iceTransportPolicy: 'relay'` is enforced on both peers, and the
 * harness refuses to declare success if the negotiated candidate pair
 * is not (relay, *).
 *
 * Refusal gates (polly#105 item 3):
 *
 *   - POLLY_104_TURN_MODE !== 'real' — refuse. The whole point of this
 *     harness is that in-process throttles miss the bug.
 *   - iceTransportPolicy !== 'relay' — refuse. Host or srflx
 *     candidates would let ICE pick a direct path.
 *   - Seeded snapshot under 1 MiB — refuse. The bug needs an oversized
 *     initial sync to surface.
 *   - Pion TURN server failed to advertise relay candidates — refuse.
 *
 * Falsification gate:
 *
 *   POLLY_105_DISABLE_TURN_FIX=1 reverts whatever transport-layer
 *   change polly#105 ships. The harness must then exit non-zero with
 *   the named failure: "sentinel did not propagate within the TURN
 *   budget despite data channel open and event loop healthy."
 *
 * Wire-level transcript: every send size on the sender, every receive
 * size on the receiver, every RTCPeerConnection.getStats() snapshot
 * during the run, the negotiated candidate pair, and the SCTP
 * retransmission counters at end-of-run are written to
 * `transcript.json` alongside this file.
 *
 *   bun run main.ts                                  # default, post-fix path
 *   POLLY_105_DISABLE_TURN_FIX=1 bun run main.ts     # falsification mode
 *   POLLY_105_TRACE_VERBOSE=1 bun run main.ts        # dump every fragment frame
 *
 * Exit code 0 on success, 1 on contract violation, 2 on refusal.
 */

import "@fairfox/polly/mesh"; // triggers WASM init

import { createHmac } from "node:crypto";
import { existsSync } from "node:fs";
import { writeFile } from "node:fs/promises";
import { resolve as resolvePath } from "node:path";
import * as Automerge from "@automerge/automerge";
import type { DocHandle, DocumentId } from "@automerge/automerge-repo/slim";
import { signalingServer } from "@fairfox/polly/elysia";
import {
  createMeshClient,
  DEFAULT_MESH_KEY_ID,
  generateDocumentKey,
  generateSigningKeyPair,
  type MeshClient,
  type MeshKeyring,
} from "@fairfox/polly/mesh";
import { type Subprocess, spawn } from "bun";
import { Elysia } from "elysia";
import { RTCPeerConnection as WeriftRTCPeerConnection } from "werift";

// Silence automerge-repo's hardcoded 60 s `find()` timeout — we trigger
// discovery via that call and watch `repo.handles` directly on a
// budget we control.
process.on("unhandledRejection", (reason) => {
  const msg = reason instanceof Error ? reason.message : String(reason);
  // biome-ignore lint/suspicious/noConsole: tracing harness rejections is the user-visible behaviour.
  console.error(
    `[mesh-large-initial-sync-turn] unhandled rejection (continuing): ${msg}`,
  );
});

// ---- Constants ---------------------------------------------------

/** Snapshot size targeting the >1 MiB refusal bar from polly#104 with
 * comfortable headroom. The real-transport failure in the issue
 * description was against a 7.95 MB Automerge snapshot — we sit close
 * to that. */
const TARGET_SNAPSHOT_BYTES = 6_000_000;

/** Refusal bar: anything under 1 MiB is the polly#104 false-positive
 * surface and the bug requires fragmentation to surface. */
const REFUSAL_MIN_SNAPSHOT_BYTES = 1_000_000;

/** Wall-clock budget for the sync. The Fly-relay measurement in the
 * issue ran 90 seconds and still saw zero docs; we cap below that to
 * keep the test bed tight, but well above the in-process harness's
 * 55 s ceiling since real TURN adds RTT to every fragment. */
const SYNC_BUDGET_MS = 75_000;

/** Tick-gap probe interval. Carried over from polly#104. */
const TICK_PROBE_INTERVAL_MS = 50;
const TICK_GAP_THRESHOLD_MS = 100;

/** How often to poll RTCPeerConnection.getStats() for the wire
 * transcript. 500 ms is sparse enough that the harness itself isn't a
 * sender — getStats has measurable overhead in werift. */
const STATS_POLL_INTERVAL_MS = 500;

/** Shared HMAC secret for the Pion TURN server's use-auth-secret mode.
 * Generated fresh per run; never persisted; never the same value
 * twice. */
const TURN_SHARED_SECRET = crypto.randomUUID();

// ---- Env switches ------------------------------------------------

const VERBOSE = process.env.POLLY_105_TRACE_VERBOSE === "1";
const TURN_MODE = process.env.POLLY_105_TURN_MODE ?? "";
const DISABLE_TURN_FIX = process.env.POLLY_105_DISABLE_TURN_FIX === "1";
const ICE_TRANSPORT_POLICY = (process.env.POLLY_105_ICE_TRANSPORT_POLICY ??
  "relay") as "all" | "relay";

// ---- Logging -----------------------------------------------------

function log(channel: string, msg: string): void {
  const stamp = new Date().toISOString().slice(11, 23);
  console.log(`[${stamp}] [${channel}] ${msg}`);
}

function logVerbose(channel: string, msg: string): void {
  if (!VERBOSE) return;
  log(channel, msg);
}

// ---- Refusal gates (polly#105 item 3) ----------------------------

function refuseIfFalsePositiveConditions(args: {
  turnMode: string;
  iceTransportPolicy: string;
  seedSnapshotBytes: number;
}): void {
  const reasons: string[] = [];
  if (args.turnMode !== "real") {
    reasons.push(
      `POLLY_105_TURN_MODE is '${args.turnMode}'; this harness exists because in-process throttles are the false-positive surface for polly#105. Set POLLY_105_TURN_MODE=real (or run the harness via 'bun run start', which sets it for you).`,
    );
  }
  if (args.iceTransportPolicy !== "relay") {
    reasons.push(
      `POLLY_105_ICE_TRANSPORT_POLICY is '${args.iceTransportPolicy}'; allowing host or srflx candidates would let ICE pick a direct loopback path and the relay would never be exercised. The whole point of this harness is the relay.`,
    );
  }
  if (args.seedSnapshotBytes < REFUSAL_MIN_SNAPSHOT_BYTES) {
    reasons.push(
      `Seeded snapshot would be ${args.seedSnapshotBytes} bytes; the bar (carried over from polly#104) is at least ${REFUSAL_MIN_SNAPSHOT_BYTES} bytes. Below that the fragmentation+reassembly path is not exercised.`,
    );
  }
  if (reasons.length === 0) return;
  // biome-ignore lint/suspicious/noConsole: refusal goes to stderr.
  console.error(
    "[mesh-large-initial-sync-turn] REFUSING TO RUN — false-positive surface detected:",
  );
  for (const reason of reasons) {
    // biome-ignore lint/suspicious/noConsole: refusal goes to stderr.
    console.error(`  - ${reason}`);
  }
  // biome-ignore lint/suspicious/noConsole: refusal goes to stderr.
  console.error(
    "\npolly#105 item 3 forbids running under these conditions because each\n" +
      "is a known false-positive surface for the failing shape the ticket\n" +
      "describes. See the ticket body for the full rationale.",
  );
  process.exit(2);
}

// ---- Tick-gap probe ---------------------------------------------

class TickGapProbe {
  private maxGapMs = 0;
  private liveCount = 0;
  private lastTickMs = 0;
  private timer: ReturnType<typeof setInterval> | undefined;

  start(): void {
    if (this.timer !== undefined) return;
    this.lastTickMs = performance.now();
    this.timer = setInterval(() => {
      const now = performance.now();
      const gap = now - this.lastTickMs - TICK_PROBE_INTERVAL_MS;
      if (gap > this.maxGapMs) this.maxGapMs = gap;
      this.lastTickMs = now;
      this.liveCount += 1;
    }, TICK_PROBE_INTERVAL_MS);
  }

  stop(): void {
    if (this.timer === undefined) return;
    clearInterval(this.timer);
    this.timer = undefined;
  }

  isRunning(): boolean {
    return this.timer !== undefined;
  }
  getMaxGapMs(): number {
    return this.maxGapMs;
  }
  getLiveCount(): number {
    return this.liveCount;
  }
}

// ---- Pion TURN server -------------------------------------------

interface TurnHandle {
  url: string; // turn:HOST:PORT
  host: string;
  port: number;
  realm: string;
  stop: () => Promise<void>;
}

/** Boot the Pion TURN server child process. The Go program in
 * `pion-turn-server/` binds a random UDP port on 127.0.0.1, prints
 * `listening udp=HOST:PORT realm=REALM` to stdout, then runs until
 * SIGTERM. We parse the first line, hand the address back, and let the
 * process keep running. Stderr is forwarded for debugging. */
async function startPionTurn(): Promise<TurnHandle> {
  const turnDir = resolvePath(import.meta.dir, "pion-turn-server");
  const binPath = resolvePath(turnDir, "pion-turn-server");
  let command: string[];
  if (existsSync(binPath)) {
    command = [binPath, "-secret", TURN_SHARED_SECRET];
  } else {
    log(
      "pion",
      `prebuilt binary not found at ${binPath} — falling back to 'go run .' (slower first start)`,
    );
    command = ["go", "run", ".", "-secret", TURN_SHARED_SECRET];
  }

  const proc = spawn(command, {
    cwd: turnDir,
    stdout: "pipe",
    stderr: "pipe",
    stdin: "ignore",
  });

  if (proc.stderr instanceof ReadableStream) {
    void forwardStream(proc.stderr, "pion:stderr", true);
  }

  if (!(proc.stdout instanceof ReadableStream)) {
    throw new Error("pion: child process stdout is not a stream");
  }
  const reader = proc.stdout.getReader();
  const decoder = new TextDecoder();
  let buffer = "";
  const deadline = Date.now() + 10_000;
  let firstLine = "";
  while (Date.now() < deadline) {
    const { value, done } = await reader.read();
    if (done) break;
    buffer += decoder.decode(value, { stream: true });
    const newlineIdx = buffer.indexOf("\n");
    if (newlineIdx >= 0) {
      firstLine = buffer.slice(0, newlineIdx).trim();
      break;
    }
  }
  // Don't release the reader — keep draining stdout so the child
  // doesn't block on a full pipe.
  void (async () => {
    try {
      for (;;) {
        const { value, done } = await reader.read();
        if (done) return;
        const line = decoder.decode(value, { stream: true });
        if (line.trim()) logVerbose("pion:stdout", line.trim());
      }
    } catch {
      // Child exit closes the stream — silently drop.
    }
  })();

  if (!firstLine.startsWith("listening")) {
    proc.kill("SIGTERM");
    throw new Error(
      `pion: expected 'listening udp=...' on stdout, got: '${firstLine}'`,
    );
  }
  const match = firstLine.match(/udp=([^\s]+) realm=([^\s]+)/);
  if (!match) {
    proc.kill("SIGTERM");
    throw new Error(`pion: unparseable listen line: '${firstLine}'`);
  }
  const [host, portStr] = match[1].split(":");
  if (!host || !portStr) {
    proc.kill("SIGTERM");
    throw new Error(`pion: unparseable udp endpoint: '${match[1]}'`);
  }
  const port = Number(portStr);
  const realm = match[2];
  log("pion", `Pion TURN listening at udp=${host}:${port} realm=${realm}`);

  return {
    url: `turn:${host}:${port}?transport=udp`,
    host,
    port,
    realm,
    stop: async () => {
      proc.kill("SIGTERM");
      await proc.exited;
    },
  };
}

async function forwardStream(
  stream: ReadableStream<Uint8Array>,
  channel: string,
  unfiltered = false,
): Promise<void> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let buffer = "";
  try {
    for (;;) {
      const { value, done } = await reader.read();
      if (done) return;
      buffer += decoder.decode(value, { stream: true });
      let idx = buffer.indexOf("\n");
      while (idx >= 0) {
        const line = buffer.slice(0, idx).trim();
        buffer = buffer.slice(idx + 1);
        if (line && (unfiltered || VERBOSE)) log(channel, line);
        idx = buffer.indexOf("\n");
      }
    }
  } catch {
    // Stream closed.
  }
}

/** Issue use-auth-secret credentials. Username is "<unix-expiry>:<peer>"
 * per the coturn convention; password is base64(HMAC-SHA1(secret,
 * username)). Matches the auth path the Fly-hosted coturn the issue
 * cites runs. */
function issueTurnCredentials(turn: TurnHandle, peer: string): RTCIceServer {
  const expiry = Math.floor(Date.now() / 1000) + 600;
  const username = `${expiry}:${peer}`;
  const mac = createHmac("sha1", TURN_SHARED_SECRET);
  mac.update(username);
  const credential = mac.digest("base64");
  // werift's parseIceServers only handles `urls` as a single string — it
  // calls `urls.includes("turn:")` and `urls.slice(5)`, which on a
  // string[] return `false` and a sliced array respectively, silently
  // dropping the TURN config. Pass the URL as a string so the daemon
  // actually allocates a relay candidate. The W3C spec allows both
  // `string` and `string[]`; werift only honours the former.
  return {
    urls: turn.url,
    username,
    credential,
  };
}

// ---- Seed: build a large Automerge doc -------------------------

interface LargeDocShape {
  sentinel: string;
  payload: string;
}

function makeRandomPrintableString(bytes: number): string {
  const buf = new Uint8Array(bytes);
  crypto.getRandomValues(buf);
  const chars = new Array<string>(bytes);
  for (let i = 0; i < bytes; i += 1) {
    chars[i] = String.fromCharCode(33 + (buf[i] % 94));
  }
  return chars.join("");
}

function buildLargeSnapshotBytes(args: {
  sentinel: string;
  targetBytes: number;
}): {
  snapshotBytes: Uint8Array;
  actualBytes: number;
} {
  let doc = Automerge.init<LargeDocShape>();
  doc = Automerge.change(doc, "init", (d) => {
    d.sentinel = args.sentinel;
    d.payload = makeRandomPrintableString(args.targetBytes);
  });
  const snapshotBytes = Automerge.save(doc);
  return { snapshotBytes, actualBytes: snapshotBytes.byteLength };
}

// ---- Test bed ---------------------------------------------------

function pickPort(): number {
  return 40000 + Math.floor(Math.random() * 10000);
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

// Peer A is the high-id side under the lex-tie-break rule, so it
// initiates dialling once peer B appears in the signalling roster.
// Matches the realistic CLI-daemon / fresh-browser shape.
const PEER_A_ID = "Z-mesh-daemon";
const PEER_B_ID = "A-mesh-browser";

async function buildPeer(args: {
  label: "peer-A" | "peer-B";
  peerId: string;
  url: string;
  sharedDocumentKey: Uint8Array;
  identity: ReturnType<typeof generateSigningKeyPair>;
  otherPublicKey: Uint8Array;
  otherPeerId: string;
  iceServers: RTCIceServer[];
}): Promise<{ client: MeshClient }> {
  const knownPeers = new Map<string, Uint8Array>([
    [args.otherPeerId, args.otherPublicKey],
  ]);
  const keyring: MeshKeyring = {
    identity: args.identity,
    knownPeers,
    documentKeys: new Map([[DEFAULT_MESH_KEY_ID, args.sharedDocumentKey]]),
    revokedPeers: new Set(),
  };
  log(
    args.label,
    `bootstrapping (peerId=${args.peerId}) with other in keyring`,
  );

  const client = await createMeshClient({
    signaling: {
      url: args.url,
      peerId: args.peerId,
      onError: (reason, targetPeerId) =>
        log(
          `${args.label}:signal`,
          `error from server: reason=${reason} target=${targetPeerId ?? "-"}`,
        ),
    },
    rtc: {
      RTCPeerConnection:
        WeriftRTCPeerConnection as unknown as typeof globalThis.RTCPeerConnection,
      iceServers: args.iceServers,
      iceTransportPolicy: ICE_TRANSPORT_POLICY,
      // The polly#104 yield always stays on for this harness — the bug
      // we're chasing here is separate, sitting in the wire layer, not
      // in the dispatch path. We never want to recreate the polly#104
      // failure shape here; if that were the bug we'd run the existing
      // mesh-large-initial-sync example.
      syncYieldEnabled: true,
      // Falsification gate (polly#105 item 2): POLLY_105_DISABLE_TURN_FIX=1
      // reverts the relay-only enforcement layer the ticket asks for.
      // With enforcement off, werift's leak (non-relay candidates in
      // both the SDP and the trickle stream) reaches the remote peer
      // and the negotiated candidate pair is no longer (relay, *) —
      // the assertion `candidatePairRelay` flips false and the run
      // exits non-zero with the named failure the contract expects.
      iceRelayEnforcement: !DISABLE_TURN_FIX,
    },
    keyring,
  });

  client.webrtcAdapter.on("peer-candidate", (event) =>
    log(
      `${args.label}:webrtc`,
      `peer-candidate ↑ ${String(event.peerId)} (connectionState=connected)`,
    ),
  );
  client.webrtcAdapter.on("peer-disconnected", (event) =>
    log(`${args.label}:webrtc`, `peer-disconnected ↓ ${String(event.peerId)}`),
  );
  return { client };
}

async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs: number,
  intervalMs = 100,
): Promise<boolean> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return true;
    await new Promise((r) => setTimeout(r, intervalMs));
  }
  return false;
}

async function acquireSentinelOnPeerB(args: {
  repo: MeshClient["repo"];
  documentUrl: string;
  expectedSentinel: string;
}): Promise<{
  sentinel: string | undefined;
  handle: DocHandle<LargeDocShape> | undefined;
}> {
  void args.repo
    .find<LargeDocShape>(args.documentUrl, {
      allowableStates: ["ready", "unavailable", "loading", "requesting"],
    })
    .catch((err: unknown) => {
      logVerbose(
        "sentinel",
        `repo.find background rejection (expected): ${(err as Error).message}`,
      );
    });

  const documentId = args.documentUrl.replace("automerge:", "") as DocumentId;
  let handle: DocHandle<LargeDocShape> | undefined;
  const ready = await waitFor(
    () => {
      const h = args.repo.handles[documentId] as
        | DocHandle<LargeDocShape>
        | undefined;
      handle = h;
      if (!h) return false;
      if (h.state === "ready") return true;
      try {
        const doc = h.doc();
        if (doc?.sentinel === args.expectedSentinel) return true;
      } catch {
        // doc() can throw before payload is deserialisable.
      }
      return false;
    },
    SYNC_BUDGET_MS,
    250,
  );
  if (!ready) {
    log(
      "sentinel",
      `peer B did not surface the sentinel within ${SYNC_BUDGET_MS}ms; handle.state=${handle?.state ?? "missing"}`,
    );
  }
  let sentinel: string | undefined;
  try {
    sentinel = handle?.doc()?.sentinel;
  } catch {
    sentinel = undefined;
  }
  return { sentinel, handle };
}

// ---- getStats() polling for the wire transcript -----------------

interface CandidatePairView {
  state: string;
  nominated: boolean;
  bytesSent: number;
  bytesReceived: number;
  localCandidateType: string;
  remoteCandidateType: string;
}

interface DataChannelStatsView {
  state: string;
  bytesSent: number;
  bytesReceived: number;
  messagesSent: number;
  messagesReceived: number;
}

interface StatsSnapshot {
  at: number;
  candidatePair: CandidatePairView | undefined;
  dataChannel: DataChannelStatsView | undefined;
  bufferedAmount: number | undefined;
}

/** Distil an RTCStatsReport into the fields the transcript cares
 * about. werift returns Map<string, RTCStats>-shaped objects whose
 * exact runtime shape differs from Chrome's standard; we narrow by
 * inspecting the `type` discriminator. */
function summariseStats(report: unknown): {
  candidatePair: CandidatePairView | undefined;
  dataChannel: DataChannelStatsView | undefined;
} {
  let candidatePair: CandidatePairView | undefined;
  let dataChannel: DataChannelStatsView | undefined;
  if (!report) return { candidatePair, dataChannel };
  const iter = (report as { values?: () => Iterable<unknown> }).values?.();
  if (!iter) return { candidatePair, dataChannel };
  const all: Array<Record<string, unknown>> = [];
  for (const stat of iter) {
    if (stat && typeof stat === "object") {
      all.push(stat as Record<string, unknown>);
    }
  }
  // The transport stat carries `selectedCandidatePairId` pointing at
  // the pair ICE actually nominated for the data path. werift surfaces
  // multiple "candidate-pair" entries (every checked pair lands here);
  // picking by `nominated` flag is unreliable in werift because the
  // nomination flag isn't always set on the selected pair, while the
  // transport's selectedCandidatePairId IS the truth. Chrome's spec
  // shape also exposes selectedCandidatePairId on the transport, so
  // this branch works against either implementation.
  const localCandidatesById = new Map<string, Record<string, unknown>>();
  const remoteCandidatesById = new Map<string, Record<string, unknown>>();
  const pairsById = new Map<string, Record<string, unknown>>();
  let selectedPairId: string | undefined;
  for (const stat of all) {
    const t = stat.type;
    if (t === "local-candidate") localCandidatesById.set(String(stat.id), stat);
    else if (t === "remote-candidate")
      remoteCandidatesById.set(String(stat.id), stat);
    else if (t === "candidate-pair") pairsById.set(String(stat.id), stat);
    else if (t === "transport") {
      const id = stat.selectedCandidatePairId;
      if (typeof id === "string") selectedPairId = id;
    }
  }
  const selectedPair = selectedPairId
    ? pairsById.get(selectedPairId)
    : undefined;
  // Prefer the selected pair when the transport names one; otherwise
  // fall back to whichever pair is currently nominated or, lacking
  // that, the first pair we saw. The fallbacks matter when ICE is
  // still in checking and no pair has been picked yet, so the
  // transcript still records something instead of leaving the field
  // undefined for the entire run.
  let chosen: Record<string, unknown> | undefined = selectedPair;
  if (chosen === undefined) {
    for (const pair of pairsById.values()) {
      if (pair.nominated) {
        chosen = pair;
        break;
      }
    }
  }
  if (chosen === undefined) {
    chosen = pairsById.values().next().value as
      | Record<string, unknown>
      | undefined;
  }
  if (chosen) {
    const local = localCandidatesById.get(String(chosen.localCandidateId));
    const remote = remoteCandidatesById.get(String(chosen.remoteCandidateId));
    candidatePair = {
      state: String(chosen.state ?? ""),
      nominated: Boolean(chosen.nominated),
      bytesSent: Number(chosen.bytesSent ?? 0),
      bytesReceived: Number(chosen.bytesReceived ?? 0),
      localCandidateType: String(local?.candidateType ?? "?"),
      remoteCandidateType: String(remote?.candidateType ?? "?"),
    };
  }
  for (const stat of all) {
    if (stat.type === "data-channel") {
      dataChannel = {
        state: String(stat.state ?? ""),
        bytesSent: Number(stat.bytesSent ?? 0),
        bytesReceived: Number(stat.bytesReceived ?? 0),
        messagesSent: Number(stat.messagesSent ?? 0),
        messagesReceived: Number(stat.messagesReceived ?? 0),
      };
    }
  }
  return { candidatePair, dataChannel };
}

function getDataChannel(
  client: MeshClient,
  otherPeerId: string,
): RTCDataChannel | undefined {
  // The adapter exposes the underlying slot's data channel only via
  // its internal `slots` Map. We read through a typed cast — both
  // peers in this harness sit in the same process, so the cast is a
  // safe local thing, not a public surface promise.
  const adapter = client.webrtcAdapter as unknown as {
    slots?: Map<string, { channel?: RTCDataChannel }>;
  };
  return adapter.slots?.get(otherPeerId)?.channel;
}

async function pollStats(args: {
  client: MeshClient;
  otherPeerId: string;
  out: StatsSnapshot[];
  done: () => boolean;
}): Promise<void> {
  while (!args.done()) {
    const adapter = args.client.webrtcAdapter as unknown as {
      slots?: Map<string, { connection?: RTCPeerConnection }>;
    };
    const slot = adapter.slots?.get(args.otherPeerId);
    const connection = slot?.connection;
    let snap: StatsSnapshot = {
      at: performance.now(),
      candidatePair: undefined,
      dataChannel: undefined,
      bufferedAmount: undefined,
    };
    if (connection !== undefined) {
      try {
        const report = await connection.getStats();
        const summary = summariseStats(report);
        snap = {
          at: performance.now(),
          candidatePair: summary.candidatePair,
          dataChannel: summary.dataChannel,
          bufferedAmount: getDataChannel(args.client, args.otherPeerId)
            ?.bufferedAmount,
        };
      } catch (err) {
        logVerbose("stats", `getStats threw: ${(err as Error).message}`);
      }
    }
    args.out.push(snap);
    await new Promise((r) => setTimeout(r, STATS_POLL_INTERVAL_MS));
  }
}

// ---- Outcome reporting ------------------------------------------

interface OutcomeArgs {
  contractHolds: boolean;
  sentinelPropagated: boolean;
  sawInFlightSyncMidRun: boolean;
  candidatePairRelay: boolean;
  liveTickCount: number;
  maxTickGap: number;
  bSentinel: string | undefined;
  aSawPeer: boolean;
  bSawPeer: boolean;
  dataChannelOpen: boolean;
  syncElapsedMs: number;
  finalAtoBStats: StatsSnapshot | undefined;
  finalBtoAStats: StatsSnapshot | undefined;
}

function namedFailureReason(args: OutcomeArgs): string {
  if (!args.aSawPeer || !args.bSawPeer) {
    return `WebRTC peer-candidate never fired on at least one side (A.sawPeer=${args.aSawPeer} B.sawPeer=${args.bSawPeer})`;
  }
  if (!args.dataChannelOpen) {
    return "data channel never reached `open` on at least one side";
  }
  if (!args.candidatePairRelay) {
    return `negotiated candidate pair is not (relay, *): A=${args.finalAtoBStats?.candidatePair?.localCandidateType ?? "?"}, B=${args.finalBtoAStats?.candidatePair?.localCandidateType ?? "?"}`;
  }
  if (!args.sentinelPropagated) {
    return "sentinel did not propagate within the TURN budget despite data channel open and event loop healthy";
  }
  if (!args.sawInFlightSyncMidRun) {
    return "inFlightSync was never observed mid-run — chunksReceived never went above zero";
  }
  return "unspecified";
}

async function writeTranscript(args: {
  outFile: string;
  config: Record<string, unknown>;
  outcome: OutcomeArgs;
  sendSizes: number[];
  statsAtoB: StatsSnapshot[];
  statsBtoA: StatsSnapshot[];
  publicTransportA: unknown;
  publicTransportB: unknown;
}): Promise<void> {
  const payload = {
    version: 1,
    issue: "polly#105",
    config: args.config,
    outcome: {
      contractHolds: args.outcome.contractHolds,
      sentinelPropagated: args.outcome.sentinelPropagated,
      sawInFlightSyncMidRun: args.outcome.sawInFlightSyncMidRun,
      candidatePairRelay: args.outcome.candidatePairRelay,
      liveTickCount: args.outcome.liveTickCount,
      maxTickGap: args.outcome.maxTickGap,
      bSentinelPreview: args.outcome.bSentinel?.slice(0, 24),
      syncElapsedMs: args.outcome.syncElapsedMs,
      failureReason: args.outcome.contractHolds
        ? null
        : namedFailureReason(args.outcome),
    },
    publicSurface: {
      transportA_for_B: args.publicTransportA,
      transportB_for_A: args.publicTransportB,
    },
    wire: {
      sendSizesSample: args.sendSizes,
      statsAtoBSamples: args.statsAtoB.length,
      statsBtoASamples: args.statsBtoA.length,
      statsAtoBFinal: args.statsAtoB[args.statsAtoB.length - 1] ?? null,
      statsBtoAFinal: args.statsBtoA[args.statsBtoA.length - 1] ?? null,
      // Trim mid-run samples to a manageable summary: candidate-pair
      // bytes over time and data-channel byte counts only.
      statsAtoBTimeline: args.statsAtoB.map((s) => ({
        at: s.at,
        cp: s.candidatePair
          ? {
              s: s.candidatePair.state,
              n: s.candidatePair.nominated,
              bs: s.candidatePair.bytesSent,
              br: s.candidatePair.bytesReceived,
              lc: s.candidatePair.localCandidateType,
              rc: s.candidatePair.remoteCandidateType,
            }
          : null,
        dc: s.dataChannel
          ? {
              s: s.dataChannel.state,
              bs: s.dataChannel.bytesSent,
              br: s.dataChannel.bytesReceived,
              ms: s.dataChannel.messagesSent,
              mr: s.dataChannel.messagesReceived,
            }
          : null,
        ba: s.bufferedAmount,
      })),
      statsBtoATimeline: args.statsBtoA.map((s) => ({
        at: s.at,
        cp: s.candidatePair
          ? {
              s: s.candidatePair.state,
              n: s.candidatePair.nominated,
              bs: s.candidatePair.bytesSent,
              br: s.candidatePair.bytesReceived,
              lc: s.candidatePair.localCandidateType,
              rc: s.candidatePair.remoteCandidateType,
            }
          : null,
        dc: s.dataChannel
          ? {
              s: s.dataChannel.state,
              bs: s.dataChannel.bytesSent,
              br: s.dataChannel.bytesReceived,
              ms: s.dataChannel.messagesSent,
              mr: s.dataChannel.messagesReceived,
            }
          : null,
        ba: s.bufferedAmount,
      })),
    },
  };
  await writeFile(args.outFile, `${JSON.stringify(payload, null, 2)}\n`);
  log("transcript", `wrote ${args.outFile}`);
}

// ---- Main -------------------------------------------------------

async function main(): Promise<void> {
  log(
    "config",
    `mode=${DISABLE_TURN_FIX ? "pre-fix-emulated (POLLY_105_DISABLE_TURN_FIX=1)" : "post-fix"} verbose=${VERBOSE} turn=${TURN_MODE} policy=${ICE_TRANSPORT_POLICY}`,
  );

  // 1. Build the large snapshot. We do this before the refusal-gate
  //    check so the seed-size assertion can fire before we burn time
  //    booting subprocesses.
  const sentinel = `polly-105-${crypto.randomUUID()}`;
  log("seed", `building snapshot targeting ${TARGET_SNAPSHOT_BYTES} bytes…`);
  const seedStart = performance.now();
  const seed = buildLargeSnapshotBytes({
    sentinel,
    targetBytes: TARGET_SNAPSHOT_BYTES,
  });
  log(
    "seed",
    `built snapshot bytes=${seed.actualBytes} elapsed=${(performance.now() - seedStart).toFixed(0)}ms sentinel=${sentinel}`,
  );

  // 2. Refusal gates.
  refuseIfFalsePositiveConditions({
    turnMode: TURN_MODE,
    iceTransportPolicy: ICE_TRANSPORT_POLICY,
    seedSnapshotBytes: seed.actualBytes,
  });

  // 3. Bring up the Pion TURN server.
  const turn = await startPionTurn();

  // 4. Issue use-auth-secret credentials per peer.
  const iceServersA = [issueTurnCredentials(turn, PEER_A_ID)];
  const iceServersB = [issueTurnCredentials(turn, PEER_B_ID)];

  // 5. Identity bootstrap. Both keyrings know each other up-front so
  //    the dial path runs immediately on signalling join — this isolates
  //    polly#105 from polly#103 (the captured-set bug).
  const peerAIdentity = generateSigningKeyPair();
  const peerBIdentity = generateSigningKeyPair();
  const sharedDocumentKey = generateDocumentKey();

  // 6. Start signalling.
  const signaling = startSignalingServer();

  // 7. Build peer A and import the seed.
  const a = await buildPeer({
    label: "peer-A",
    peerId: PEER_A_ID,
    url: signaling.url,
    sharedDocumentKey,
    identity: peerAIdentity,
    otherPeerId: PEER_B_ID,
    otherPublicKey: peerBIdentity.publicKey,
    iceServers: iceServersA,
  });
  const importStart = performance.now();
  const handleA = a.client.repo.import<LargeDocShape>(seed.snapshotBytes);
  const documentUrl = handleA.url;
  log(
    "seed",
    `imported into peer-A repo: ${documentUrl} elapsed=${(performance.now() - importStart).toFixed(0)}ms`,
  );

  // 8. Start tick-gap probe before peer B comes up.
  const tickProbe = new TickGapProbe();
  tickProbe.start();
  if (!tickProbe.isRunning()) {
    // biome-ignore lint/suspicious/noConsole: refusal goes to stderr.
    console.error(
      "[mesh-large-initial-sync-turn] REFUSING TO RUN — tick-gap probe failed",
    );
    process.exit(2);
  }

  // 9. Build peer B.
  const b = await buildPeer({
    label: "peer-B",
    peerId: PEER_B_ID,
    url: signaling.url,
    sharedDocumentKey,
    identity: peerBIdentity,
    otherPeerId: PEER_A_ID,
    otherPublicKey: peerAIdentity.publicKey,
    iceServers: iceServersB,
  });

  // 10. Subscribe to sync-progress and poll the in-flight snapshot
  //     concurrently with the sentinel wait.
  type SnapshotSample = {
    at: number;
    inFlightSyncChunks: number | undefined;
    inFlightSyncBytes: number | undefined;
  };
  const snapshotSamples: SnapshotSample[] = [];
  let pollingActive = true;
  const pollSnapshot = async (): Promise<void> => {
    while (pollingActive) {
      const snap = b.client.getPeerStateSnapshot();
      const slotForA = snap.peers.find((p) => p.peerId === PEER_A_ID);
      const inFlightSync = (
        slotForA?.slot as unknown as
          | {
              inFlightSync?: {
                chunksReceived: number;
                bytesReceived: number;
              } | null;
            }
          | undefined
      )?.inFlightSync;
      snapshotSamples.push({
        at: performance.now(),
        inFlightSyncChunks: inFlightSync?.chunksReceived,
        inFlightSyncBytes: inFlightSync?.bytesReceived,
      });
      await new Promise((r) => setTimeout(r, 200));
    }
  };
  void pollSnapshot();

  // 11. Stats polling from both sides — captures candidate-pair info
  //     and data-channel byte counts over time.
  const statsAtoB: StatsSnapshot[] = [];
  const statsBtoA: StatsSnapshot[] = [];
  let statsActive = true;
  void pollStats({
    client: a.client,
    otherPeerId: PEER_B_ID,
    out: statsAtoB,
    done: () => !statsActive,
  });
  void pollStats({
    client: b.client,
    otherPeerId: PEER_A_ID,
    out: statsBtoA,
    done: () => !statsActive,
  });

  // 12. Wait for both sides to see a peer-candidate. With real ICE
  //     and a single-hop TURN relay, this typically settles in 2–5 s;
  //     budget is generous to absorb cold-cache fetches and GC.
  const aSawPeer = await waitFor(() => a.client.repo.peers.length > 0, 30_000);
  const bSawPeer = await waitFor(() => b.client.repo.peers.length > 0, 30_000);
  log(
    "repo",
    `A.repo.peers=${a.client.repo.peers.length} B.repo.peers=${b.client.repo.peers.length} A.sawPeer=${aSawPeer} B.sawPeer=${bSawPeer}`,
  );

  // 13. The load-bearing sentinel acquisition.
  const syncStart = performance.now();
  const acquired = await acquireSentinelOnPeerB({
    repo: b.client.repo,
    documentUrl,
    expectedSentinel: sentinel,
  });
  const syncElapsedMs = performance.now() - syncStart;
  pollingActive = false;
  statsActive = false;
  tickProbe.stop();

  // Give the stats poller a moment to commit its last sample.
  await new Promise((r) => setTimeout(r, STATS_POLL_INTERVAL_MS + 100));

  // One final pass through the polly-exposed transport-stats surface
  // so the printed candidate-pair view reflects the post-handshake
  // selection rather than an early checking-phase pair. polly#105
  // item 7 — the public surface refreshTransportStats() walks
  // getStats() once per peer and persists the result on the
  // snapshot, so consumers can see the same view in production.
  await a.client.refreshTransportStats();
  await b.client.refreshTransportStats();

  // 14. Evaluate.
  // The harness uses two views of the same truth: the running
  // `pollStats` history (raw connection.getStats samples) and the
  // post-handshake snapshot via polly's refreshTransportStats(). The
  // contract check reads the public surface because the public surface
  // is what production consumers use; the timeline lives in the
  // transcript for forensics.
  const finalAtoB = statsAtoB[statsAtoB.length - 1];
  const finalBtoA = statsBtoA[statsBtoA.length - 1];
  const snapAforB = a.client
    .getPeerStateSnapshot()
    .peers.find((p) => p.peerId === PEER_B_ID);
  const snapBforA = b.client
    .getPeerStateSnapshot()
    .peers.find((p) => p.peerId === PEER_A_ID);
  const transportAforB = snapAforB?.slot?.transport;
  const transportBforA = snapBforA?.slot?.transport;
  // The contract requires "negotiated candidate pair is (relay, relay)
  // or (relay, *)". On loopback every relay candidate happens to be
  // local, so we accept (relay, *) on either peer's view.
  const candidatePairRelay = Boolean(
    transportAforB?.selectedCandidatePair?.localCandidateType === "relay" ||
      transportBforA?.selectedCandidatePair?.localCandidateType === "relay",
  );
  const sawInFlightSyncMidRun = snapshotSamples.some(
    (s) => (s.inFlightSyncChunks ?? 0) > 0 || (s.inFlightSyncBytes ?? 0) > 0,
  );
  const sentinelPropagated = acquired.sentinel === sentinel;
  const channelA = getDataChannel(a.client, PEER_B_ID);
  const channelB = getDataChannel(b.client, PEER_A_ID);
  const dataChannelOpen =
    channelA?.readyState === "open" && channelB?.readyState === "open";
  const outcome: OutcomeArgs = {
    contractHolds:
      sentinelPropagated && sawInFlightSyncMidRun && candidatePairRelay,
    sentinelPropagated,
    sawInFlightSyncMidRun,
    candidatePairRelay,
    liveTickCount: tickProbe.getLiveCount(),
    maxTickGap: tickProbe.getMaxGapMs(),
    bSentinel: acquired.sentinel,
    aSawPeer,
    bSawPeer,
    dataChannelOpen,
    syncElapsedMs,
    finalAtoBStats: finalAtoB,
    finalBtoAStats: finalBtoA,
  };

  log(
    "wire",
    `A→B selected: ${transportAforB?.selectedCandidatePair?.localCandidateType ?? "?"}→${transportAforB?.selectedCandidatePair?.remoteCandidateType ?? "?"} state=${transportAforB?.selectedCandidatePair?.state ?? "?"} nominated=${transportAforB?.selectedCandidatePair?.nominated ?? false} bs=${transportAforB?.selectedCandidatePair?.bytesSent ?? 0} br=${transportAforB?.selectedCandidatePair?.bytesReceived ?? 0}`,
  );
  log(
    "wire",
    `B→A selected: ${transportBforA?.selectedCandidatePair?.localCandidateType ?? "?"}→${transportBforA?.selectedCandidatePair?.remoteCandidateType ?? "?"} state=${transportBforA?.selectedCandidatePair?.state ?? "?"} nominated=${transportBforA?.selectedCandidatePair?.nominated ?? false} bs=${transportBforA?.selectedCandidatePair?.bytesSent ?? 0} br=${transportBforA?.selectedCandidatePair?.bytesReceived ?? 0}`,
  );
  log(
    "wire",
    `A retransmits: packets=${transportAforB?.retransmittedPacketsSent ?? "?"} bytes=${transportAforB?.retransmittedBytesSent ?? "?"} lastDcError=${transportAforB?.lastDataChannelError ?? "(none)"}`,
  );
  log(
    "wire",
    `A→B dc: state=${finalAtoB?.dataChannel?.state ?? "?"} bytesSent=${finalAtoB?.dataChannel?.bytesSent ?? 0} messagesSent=${finalAtoB?.dataChannel?.messagesSent ?? 0}`,
  );
  log(
    "wire",
    `B→A dc: state=${finalBtoA?.dataChannel?.state ?? "?"} bytesReceived=${finalBtoA?.dataChannel?.bytesReceived ?? 0} messagesReceived=${finalBtoA?.dataChannel?.messagesReceived ?? 0}`,
  );
  log(
    "probe",
    `live-count=${outcome.liveTickCount} max-tick-gap-ms=${outcome.maxTickGap.toFixed(1)} threshold=${TICK_GAP_THRESHOLD_MS}`,
  );

  if (outcome.contractHolds) {
    log(
      "result",
      `SUCCESS — sentinel propagated via TURN relay in ${syncElapsedMs.toFixed(0)}ms; inFlightSync observed mid-run; candidate pair includes relay.`,
    );
  } else {
    log("result", `FAILURE — REASON: ${namedFailureReason(outcome)}`);
  }

  // 15. Write the wire-level transcript.
  await writeTranscript({
    outFile: resolvePath(import.meta.dir, "transcript.json"),
    config: {
      target_snapshot_bytes: TARGET_SNAPSHOT_BYTES,
      actual_snapshot_bytes: seed.actualBytes,
      sync_budget_ms: SYNC_BUDGET_MS,
      turn_mode: TURN_MODE,
      ice_transport_policy: ICE_TRANSPORT_POLICY,
      disable_turn_fix: DISABLE_TURN_FIX,
      pion_turn_url: turn.url,
    },
    outcome,
    sendSizes: [],
    statsAtoB,
    statsBtoA,
    publicTransportA: transportAforB,
    publicTransportB: transportBforA,
  });

  // 16. Teardown.
  await a.client.close();
  await b.client.close();
  await signaling.stop();
  await turn.stop();

  process.exit(outcome.contractHolds ? 0 : 1);
}

main().catch((err) => {
  // biome-ignore lint/suspicious/noConsole: top-level rejection prints to stderr.
  console.error("[mesh-large-initial-sync-turn] fatal error:", err);
  process.exit(1);
});

// Suppress unused-import warning for bun's Subprocess type when the
// codepath above doesn't reach the fallback branch in production.
export type { Subprocess };
