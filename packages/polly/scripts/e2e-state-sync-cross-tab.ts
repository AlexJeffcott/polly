#!/usr/bin/env bun
/**
 * E2e: $syncedState stays two-way across real browser tabs. (polly#166.)
 *
 * The defect polly#166 fixes is invisible to any single-context test. A
 * context that received one sync message stopped broadcasting, because the
 * change-watching effect returned before it read `sig.value` and Preact
 * dropped its subscription. Unit tests with a fake adapter catch it; only a
 * second real tab proves the round trip.
 *
 * So this drives the genuine article: two pages of one http origin in real
 * Chrome, the real BroadcastChannelSyncAdapter auto-detected by the
 * documented entry point (`$syncedState` from the package index — no
 * hand-wired adapter), starting from cold state.
 *
 *   1. ping   tab A writes, tab B sees it; then tab B writes and tab A sees
 *             it. Step two is the regression: on the broken code tab B never
 *             broadcasts again and this times out.
 *   2. queue  three sequential appends alternating between the tabs; both
 *             tabs converge on all three items.
 *   3. echo   a third page listens on the raw BroadcastChannel('polly-sync')
 *             and counts frames. Exactly one frame per local write — an
 *             applied update must not be echoed back to its sender.
 *
 * Scenario 3 is the guard on the naive fix: deleting the `entry.updating`
 * check makes scenario 1 pass and turns every update into a broadcast storm.
 */

export const capability = "state.cross-tab-sync" as const;

import { rm, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import puppeteer, { type Browser, type Page } from "puppeteer";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const packageRoot = resolve(import.meta.dir, "..");
const indexPath = resolve(packageRoot, "src/index.ts");
const entryPath = resolve(packageRoot, "scripts/__issue-166-entry.tmp.ts");

interface SyncFrame {
  type: string;
  key: string;
  value: unknown;
  clock: number;
}

declare global {
  interface Window {
    /** Installed by the bundled app entry below. */
    pollyE2e: {
      ping: () => string;
      setPing: (value: string) => void;
      queue: () => string[];
      append: (item: string) => void;
    };
    /** Installed by the probe page below. */
    pollyFrames: SyncFrame[];
  }
}

const PING_KEY = "e2e-166-ping";
const QUEUE_KEY = "e2e-166-queue";
const CHANNEL = "polly-sync";

/** Browser-side app. Uses the documented entry point and no explicit adapter. */
const ENTRY_SOURCE = `
import { $syncedState } from ${JSON.stringify(indexPath)};

const ping = $syncedState("${PING_KEY}", "initial");
const queue = $syncedState("${QUEUE_KEY}", []);

window.pollyE2e = {
  ping: () => ping.value,
  setPing: (value) => {
    ping.value = value;
  },
  queue: () => queue.value,
  append: (item) => {
    queue.value = [...queue.value, item];
  },
};
`;

const APP_HTML = `<!doctype html><meta charset="utf-8"><title>polly#166</title><script type="module" src="/app.js"></script>`;

/** Raw listener on the sync channel. Records every frame either tab sends. */
const PROBE_HTML = `<!doctype html><meta charset="utf-8"><title>polly#166 probe</title><script>
window.pollyFrames = [];
const channel = new BroadcastChannel(${JSON.stringify(CHANNEL)});
channel.onmessage = (event) => {
  window.pollyFrames.push(event.data);
};
</script>`;

/** Poll a page until the predicate holds, or fail with what it last saw. */
async function waitFor<T>(
  page: Page,
  read: () => T,
  predicate: (value: T) => boolean,
  what: string,
  timeoutMs = 4000
): Promise<T> {
  const deadline = Date.now() + timeoutMs;
  let last: T = await page.evaluate(read);
  while (!predicate(last)) {
    if (Date.now() >= deadline) {
      throw new Error(`${what}: timed out after ${timeoutMs}ms, last saw ${JSON.stringify(last)}`);
    }
    await new Promise((r) => setTimeout(r, 50));
    last = await page.evaluate(read);
  }
  return last;
}

export async function run(ctx: TierContext): Promise<TierResult> {
  let browser: Browser | undefined;
  let server: ReturnType<typeof Bun.serve> | undefined;
  try {
    // 1. Bundle the browser app from the working-tree source.
    ctx.log("[e2e] bundling the app from src/index.ts");
    await writeFile(entryPath, ENTRY_SOURCE, "utf8");
    const built = await Bun.build({
      entrypoints: [entryPath],
      target: "browser",
      format: "esm",
      minify: false,
    });
    assert(built.success, `bundle failed:\n${built.logs.map((l) => String(l)).join("\n")}`);
    const appJs = await built.outputs[0]?.text();
    assert(!!appJs, "bundle produced no output");

    // 2. Serve it — BroadcastChannel needs a real origin, not file://.
    server = Bun.serve({
      port: 0,
      fetch(request) {
        const { pathname } = new URL(request.url);
        if (pathname === "/app.js") {
          return new Response(appJs, {
            headers: { "content-type": "text/javascript; charset=utf-8" },
          });
        }
        if (pathname === "/probe") {
          return new Response(PROBE_HTML, {
            headers: { "content-type": "text/html; charset=utf-8" },
          });
        }
        return new Response(APP_HTML, {
          headers: { "content-type": "text/html; charset=utf-8" },
        });
      },
    });
    const origin = `http://localhost:${server.port}`;
    ctx.log(`[e2e] serving ${origin}`);

    browser = await puppeteer.launch({
      headless: true,
      args: ["--no-sandbox", "--disable-setuid-sandbox"],
    });

    // 3. Probe first, so it records every frame from both tabs.
    const probe = await browser.newPage();
    await probe.goto(`${origin}/probe`, { waitUntil: "load" });

    const tabA = await browser.newPage();
    const tabB = await browser.newPage();
    for (const [name, page] of [
      ["A", tabA],
      ["B", tabB],
    ] as const) {
      await page.goto(origin, { waitUntil: "load" });
      await page.waitForFunction("window.pollyE2e !== undefined", { timeout: 5000 });
      ctx.log(`[e2e] tab ${name} ready`);
    }

    // 4. ping — A → B, then B → A. The second leg is polly#166.
    ctx.log("[e2e] ping: A writes, B must see it");
    await tabA.evaluate(() => {
      window.pollyE2e.setPing("from-a");
    });
    await waitFor(
      tabB,
      () => window.pollyE2e.ping(),
      (v) => v === "from-a",
      "B never saw A's write"
    );

    ctx.log("[e2e] ping: B writes, A must see it (polly#166)");
    await tabB.evaluate(() => {
      window.pollyE2e.setPing("from-b");
    });
    await waitFor(
      tabA,
      () => window.pollyE2e.ping(),
      (v) => v === "from-b",
      "A never saw B's write — B stopped broadcasting after one incoming update (polly#166)"
    );

    // 5. queue — three sequential appends, alternating tabs.
    ctx.log("[e2e] queue: three sequential appends across both tabs");
    await tabA.evaluate(() => {
      window.pollyE2e.append("a1");
    });
    await waitFor(
      tabB,
      () => window.pollyE2e.queue(),
      (q) => q.length === 1,
      "B missed append a1"
    );

    await tabB.evaluate(() => {
      window.pollyE2e.append("b1");
    });
    await waitFor(
      tabA,
      () => window.pollyE2e.queue(),
      (q) => q.length === 2,
      "A missed append b1"
    );

    await tabA.evaluate(() => {
      window.pollyE2e.append("a2");
    });
    const finalB = await waitFor(
      tabB,
      () => window.pollyE2e.queue(),
      (q) => q.length === 3,
      "B missed append a2"
    );
    const finalA = await tabA.evaluate(() => window.pollyE2e.queue());
    assert(
      JSON.stringify(finalA) === JSON.stringify(["a1", "b1", "a2"]),
      `tab A converged on ${JSON.stringify(finalA)}`
    );
    assert(
      JSON.stringify(finalB) === JSON.stringify(["a1", "b1", "a2"]),
      `tab B converged on ${JSON.stringify(finalB)}`
    );

    // 6. echo — exactly one frame per local write, no echoes.
    const frames = await probe.evaluate(() => window.pollyFrames);
    const summary = frames.map((f) => `${f.key}=${JSON.stringify(f.value)}@${f.clock}`);
    ctx.log(`[e2e] frames on ${CHANNEL}: ${summary.join(" ")}`);
    assert(
      frames.length === 5,
      `expected 5 frames (one per local write), saw ${frames.length}: ${summary.join(" ")}`
    );

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    await browser?.close();
    server?.stop(true);
    await rm(entryPath, { force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
