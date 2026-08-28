#!/usr/bin/env bun
/**
 * Spike for polly#111, approach B: does moving the Automerge apply into a
 * Worker actually hold the <100ms main-thread tick-gap bar?
 *
 * This is a MEASUREMENT, not a fix. #111's own comment records that approach A
 * (splitting sync messages at the change boundary) was built and reverted,
 * because a compacted snapshot arrives as ONE Automerge change and there is
 * nothing to split. Approach B is scoped in that comment as multi-week —
 * storage-subsystem bridging, handle-lifecycle proxies, and preserving the
 * synchronous-read contract `$meshState` consumers rely on. That is a large
 * build resting on one unproven premise, so measure the premise first.
 *
 * Three readings, each with the same 50ms `setInterval` probe on the main
 * thread that `main.ts` uses, against the same ~5.5 MB single-change snapshot:
 *
 *   1. control      apply on the main thread. MUST spike, or the probe is
 *                   measuring nothing and every other reading is worthless.
 *   2. worker       the worker applies; the main thread receives the sentinel.
 *                   This is the reading approach B rests on.
 *   3. materialise  the worker posts the whole document value back, which is
 *                   what a main-thread `$meshState` read needs. The structured
 *                   clone lands ON the main thread, so this is where a
 *                   worker-hosted Repo can put the spike straight back.
 *
 * Exit code is 0 when the readings are valid (the control spiked) and 1 when
 * the control did not spike, because then the spike proves nothing. It is not
 * a gate on #111 — it is the evidence for or against building B.
 */

import * as Automerge from "@automerge/automerge";

const TICK_PROBE_INTERVAL_MS = 50;
const TICK_GAP_THRESHOLD_MS = 100;
const TARGET_SNAPSHOT_BYTES = 7_000_000;

interface LargeDocShape {
  sentinel: string;
  payload: string;
}

/** Copied from main.ts so the spike measures the same load shape. */
function makeRandomPrintableString(bytes: number): string {
  const buf = new Uint8Array(bytes);
  crypto.getRandomValues(buf);
  const chars = new Array<string>(bytes);
  for (let i = 0; i < bytes; i += 1) {
    chars[i] = String.fromCharCode(33 + (buf[i] % 94));
  }
  return chars.join("");
}

function buildSnapshot(sentinel: string): Uint8Array {
  let doc = Automerge.init<LargeDocShape>();
  doc = Automerge.change(doc, "init", (d) => {
    d.sentinel = sentinel;
    d.payload = makeRandomPrintableString(TARGET_SNAPSHOT_BYTES);
  });
  return Automerge.save(doc);
}

/** The probe from main.ts: max gap between ticks, in excess of the interval. */
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

  get maxGap(): number {
    return this.maxGapMs;
  }

  get ticks(): number {
    return this.liveCount;
  }
}

function log(tag: string, message: string): void {
  process.stdout.write(`[${tag}] ${message}\n`);
}

interface Reading {
  name: string;
  maxTickGapMs: number;
  ticks: number;
  elapsedMs: number;
  sentinelOk: boolean;
}

/** Reading 1: apply on the main thread. The control. */
async function measureMainThread(bytes: Uint8Array, sentinel: string): Promise<Reading> {
  const probe = new TickGapProbe();
  probe.start();
  // Let the probe establish a rhythm before the work starts.
  await new Promise((r) => setTimeout(r, 300));

  const started = performance.now();
  const doc = Automerge.load<LargeDocShape>(bytes);
  const elapsedMs = performance.now() - started;

  await new Promise((r) => setTimeout(r, 300));
  probe.stop();
  return {
    name: "control (apply on main thread)",
    maxTickGapMs: probe.maxGap,
    ticks: probe.ticks,
    elapsedMs,
    sentinelOk: doc.sentinel === sentinel,
  };
}

/** Readings 2 and 3: apply in a worker, then pull the value back. */
async function measureWorker(
  bytes: Uint8Array,
  sentinel: string
): Promise<{ load: Reading; materialise: Reading }> {
  const worker = new Worker(new URL("./spike-111-worker.ts", import.meta.url).href);
  const inbox: Array<(message: unknown) => void> = [];
  worker.onmessage = (event: MessageEvent) => {
    inbox.shift()?.(event.data);
  };
  const nextMessage = (): Promise<{ [k: string]: unknown }> =>
    new Promise((resolve) => {
      inbox.push((message) => {
        resolve(message as { [k: string]: unknown });
      });
    });

  const probe = new TickGapProbe();
  probe.start();
  await new Promise((r) => setTimeout(r, 300));

  // Reading 2 — the worker applies. A copy of the bytes crosses the boundary;
  // that copy is part of the cost approach B would pay, so it is measured.
  const loadStart = performance.now();
  const loadReply = nextMessage();
  worker.postMessage({ kind: "load", bytes });
  const loaded = await loadReply;
  const loadElapsed = performance.now() - loadStart;
  await new Promise((r) => setTimeout(r, 300));
  probe.stop();
  const load: Reading = {
    name: "worker apply (main thread receives the sentinel only)",
    maxTickGapMs: probe.maxGap,
    ticks: probe.ticks,
    elapsedMs: loadElapsed,
    sentinelOk: loaded["sentinel"] === sentinel,
  };
  log(
    "spike",
    `worker-side apply took ${Number(loaded["applyMs"] ?? -1).toFixed(0)}ms off the main thread`
  );

  // Reading 3 — the whole value comes back, as a main-thread read needs.
  const probe2 = new TickGapProbe();
  probe2.start();
  await new Promise((r) => setTimeout(r, 300));
  const matStart = performance.now();
  const matReply = nextMessage();
  worker.postMessage({ kind: "materialise" });
  const materialised = await matReply;
  const matElapsed = performance.now() - matStart;
  await new Promise((r) => setTimeout(r, 300));
  probe2.stop();
  const value = materialised["value"];
  const gotSentinel =
    typeof value === "object" && value !== null && "sentinel" in value
      ? (value as { sentinel: unknown }).sentinel
      : undefined;
  const materialise: Reading = {
    name: "worker -> main structured clone of the whole document value",
    maxTickGapMs: probe2.maxGap,
    ticks: probe2.ticks,
    elapsedMs: matElapsed,
    sentinelOk: gotSentinel === sentinel,
  };

  worker.terminate();
  return { load, materialise };
}

function report(readings: Reading[]): void {
  const width = Math.max(...readings.map((r) => r.name.length));
  log("spike", "");
  log("spike", `${"reading".padEnd(width)}  max-tick-gap-ms  ticks  elapsed-ms  sentinel`);
  for (const r of readings) {
    log(
      "spike",
      `${r.name.padEnd(width)}  ${r.maxTickGapMs.toFixed(1).padStart(15)}  ${String(r.ticks).padStart(5)}  ${r.elapsedMs.toFixed(0).padStart(10)}  ${r.sentinelOk ? "ok" : "MISSING"}`
    );
  }
  log("spike", "");
}

async function main(): Promise<void> {
  const sentinel = crypto.randomUUID();
  log("spike", `building a ~${TARGET_SNAPSHOT_BYTES}-byte single-change snapshot…`);
  const bytes = buildSnapshot(sentinel);
  log("spike", `snapshot bytes=${bytes.byteLength} sentinel=${sentinel.slice(0, 8)}`);

  const control = await measureMainThread(bytes, sentinel);
  const { load, materialise } = await measureWorker(bytes, sentinel);
  report([control, load, materialise]);

  if (control.maxTickGapMs <= TICK_GAP_THRESHOLD_MS) {
    log(
      "result",
      `INVALID — the control did not spike (max-tick-gap-ms=${control.maxTickGapMs.toFixed(1)} <= ${TICK_GAP_THRESHOLD_MS}). ` +
        "The probe is not measuring the apply, so neither worker reading means anything."
    );
    process.exit(1);
  }

  const workerHolds = load.maxTickGapMs < TICK_GAP_THRESHOLD_MS;
  const materialiseHolds = materialise.maxTickGapMs < TICK_GAP_THRESHOLD_MS;
  log(
    "result",
    `apply off the main thread ${workerHolds ? "HOLDS" : "DOES NOT HOLD"} the ${TICK_GAP_THRESHOLD_MS}ms bar ` +
      `(${load.maxTickGapMs.toFixed(1)}ms).`
  );
  log(
    "result",
    `returning the whole value to the main thread ${materialiseHolds ? "HOLDS" : "DOES NOT HOLD"} it ` +
      `(${materialise.maxTickGapMs.toFixed(1)}ms).`
  );
  if (workerHolds && !materialiseHolds) {
    log(
      "result",
      "So approach B moves the spike rather than removing it, unless the state bridge " +
        "returns something smaller than the document — the synchronous-read contract is the " +
        "part that needs designing, not the apply."
    );
  }
  process.exit(0);
}

await main();
