#!/usr/bin/env bun
/**
 * E2e: a debounced write never adopts another write's clock. (polly#167.)
 *
 * `doUpdate` closed over the local value but read `entry.clock` when the timer
 * fired, and by then an incoming message had raised it. The deferred write
 * therefore persisted this tab's value under the remote clock and broadcast the
 * same pair. `loadFromStorage` restores the clock, so the tab came back holding
 * the wrong value while claiming the higher clock, and every later message
 * carrying the right value at that clock was refused by the strictly-greater
 * rule. The divergence outlived the tab.
 *
 * The unit tests drive a fake adapter. This drives the genuine article: real
 * Chrome, the real `BroadcastChannelSyncAdapter` and `IndexedDBAdapter` that
 * `$sharedState` auto-detects from the documented entry point, one http origin,
 * cold storage, and a RELOAD — because the durable half of the defect is only
 * visible after the value comes back off the disk.
 *
 *   1. supersede  tab A writes with `debounceMs`; a peer's newer value lands
 *                 inside the window. After the window A holds the peer's value.
 *   2. wire       the raw `BroadcastChannel('polly-sync')` frames tab A sent.
 *                 None may pair A's superseded value with the peer's clock.
 *   3. third      a cold tab C, still at clock 0, is given every frame A sent
 *                 and then the peer's real value. C must end on the peer's
 *                 value. Pre-fix, A's stale frame at the peer's clock wins and
 *                 the real one is then refused — the stale write wins outright.
 *   4. durable    reload A. IndexedDB must hand back the peer's value, not the
 *                 superseded local one under the peer's clock.
 *   5. undisturbed  a debounced write nobody interrupts still lands, in storage
 *                 and on the wire. This is the guard on the naive fix: cancel
 *                 every pending write on any incoming message and 1-4 pass
 *                 while the primitive stops writing.
 *
 * The order is deliberate: the cheap wire and third-context assertions run
 * before the reload, so a broken build reports all of them rather than stopping
 * at the first.
 *
 * The peer is a raw `BroadcastChannel` sender rather than a third polly tab.
 * It is a real peer on the real wire; only its clock is chosen, which is what
 * lets the window be hit deterministically instead of by racing two tabs.
 *
 * Needs: Chrome (puppeteer).
 */

export const capability = "state.debounce-clock" as const;

import { rm, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import puppeteer, { type Browser, type Page } from "puppeteer";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const packageRoot = resolve(import.meta.dir, "..");
const indexPath = resolve(packageRoot, "src/index.ts");
const entryPath = resolve(packageRoot, "scripts/__issue-167-entry.tmp.ts");

/**
 * The wire format `BroadcastChannelSyncAdapter` posts and filters on. The
 * `type` discriminator is required: a frame without it is dropped by the
 * adapter's `onmessage`, so a peer that omits it is silently inert.
 */
interface SyncFrame {
  type: "STATE_SYNC";
  key: string;
  value: unknown;
  clock: number;
}

declare global {
  interface Window {
    /** Installed by the bundled app entry below. */
    pollyE2e167: {
      note: () => string;
      setNote: (value: string) => void;
      plain: () => string;
      setPlain: (value: string) => void;
      ready: Promise<void>;
    };
    /** Installed by the probe page below. */
    polly167Frames: SyncFrame[];
    /** Installed by the probe page below: send one frame as a peer would. */
    polly167Send: (frame: SyncFrame) => void;
  }
}

const NOTE_KEY = "e2e-167-note";
const PLAIN_KEY = "e2e-167-plain";
const CHANNEL = "polly-sync";
const DEBOUNCE_MS = 400;

/** The peer's clock. Far enough above 0 that a cold tab C accepts it. */
const REMOTE_CLOCK = 5;
const LOCAL_VALUE = "V_local";
const REMOTE_VALUE = "V_remote";

/** Browser-side app. The documented entry point, no hand-wired adapter. */
const ENTRY_SOURCE = `
import { $sharedState } from ${JSON.stringify(indexPath)};

const note = $sharedState("${NOTE_KEY}", "initial", { debounceMs: ${DEBOUNCE_MS} });
const plain = $sharedState("${PLAIN_KEY}", "initial", { debounceMs: ${DEBOUNCE_MS} });

window.pollyE2e167 = {
  note: () => note.value,
  setNote: (value) => {
    note.value = value;
  },
  plain: () => plain.value,
  setPlain: (value) => {
    plain.value = value;
  },
  ready: Promise.all([note.loaded, plain.loaded]).then(() => undefined),
};
`;

const APP_HTML = `<!doctype html><meta charset="utf-8"><title>polly#167</title><script type="module" src="/app.js"></script>`;

/** Raw peer on the sync channel: records every frame, and can send one. */
const PROBE_HTML = `<!doctype html><meta charset="utf-8"><title>polly#167 probe</title><script>
window.polly167Frames = [];
const channel = new BroadcastChannel(${JSON.stringify(CHANNEL)});
channel.onmessage = (event) => {
  window.polly167Frames.push(event.data);
};
window.polly167Send = (frame) => {
  channel.postMessage(frame);
};
</script>`;

/** Poll a page until the predicate holds, or fail with what it last saw. */
async function waitFor<T>(
  page: Page,
  read: () => T,
  predicate: (value: T) => boolean,
  what: string,
  timeoutMs = 6000
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

/** Open an app tab and wait for its state to finish hydrating from storage. */
async function openApp(browser: Browser, origin: string): Promise<Page> {
  const page = await browser.newPage();
  await page.goto(origin, { waitUntil: "load" });
  await page.waitForFunction("window.pollyE2e167 !== undefined", { timeout: 8000 });
  await page.evaluate(() => window.pollyE2e167.ready);
  return page;
}

export async function run(ctx: TierContext): Promise<TierResult> {
  let browser: Browser | undefined;
  let server: ReturnType<typeof Bun.serve> | undefined;
  try {
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

    // BroadcastChannel and IndexedDB both need a real origin, not file://.
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

    // The probe records every frame from the moment it opens, so it must be
    // first — and it is also the peer that sends the newer value.
    const probe = await browser.newPage();
    await probe.goto(`${origin}/probe`, { waitUntil: "load" });

    const tabA = await openApp(browser, origin);
    ctx.log("[e2e] tab A ready, storage cold");

    // 1. supersede — a local write, then the peer's newer value inside the
    //    debounce window, then the window elapses.
    ctx.log("[e2e] supersede: A writes, the peer lands a newer value mid-window");
    await tabA.evaluate((v) => {
      window.pollyE2e167.setNote(v);
    }, LOCAL_VALUE);
    await probe.evaluate(
      (frame) => {
        window.polly167Send(frame);
      },
      { type: "STATE_SYNC", key: NOTE_KEY, value: REMOTE_VALUE, clock: REMOTE_CLOCK } as SyncFrame
    );
    await waitFor(
      tabA,
      () => window.pollyE2e167.note(),
      (v) => v === REMOTE_VALUE,
      "A never took the peer's newer value"
    );
    await new Promise((r) => setTimeout(r, DEBOUNCE_MS + 400));

    const inMemory = await tabA.evaluate(() => window.pollyE2e167.note());
    assert(
      inMemory === REMOTE_VALUE,
      `after the window A holds ${JSON.stringify(inMemory)} in memory, not the peer's value`
    );

    // 2. wire — what A actually put on the channel.
    const frames = (await probe.evaluate(() => window.polly167Frames)).filter(
      (f) => f.key === NOTE_KEY
    );
    const summary = frames.map((f) => `${JSON.stringify(f.value)}@${f.clock}`);
    ctx.log(`[e2e] wire: frames on ${CHANNEL} for ${NOTE_KEY}: ${summary.join(" ") || "(none)"}`);
    const forged = frames.find((f) => f.value === LOCAL_VALUE && f.clock === REMOTE_CLOCK);
    assert(
      forged === undefined,
      `A broadcast its superseded value under the peer's clock: ${JSON.stringify(forged)}`
    );
    for (const f of frames) {
      assert(
        !(f.value === LOCAL_VALUE && f.clock >= REMOTE_CLOCK),
        `a frame pairs the local value with a clock it was not written at: ${JSON.stringify(f)}`
      );
    }

    // 3. third — a cold tab, fed A's frames and then the peer's real value.
    ctx.log("[e2e] third: a cold context replayed A's frames, then the peer's value");
    const tabC = await openApp(browser, origin);
    // C shares the origin, so its own IndexedDB already holds the settled
    // value. Drive the key it has not seen instead, from clock 0.
    const replay = frames.map((f) => ({ ...f, key: PLAIN_KEY }));
    for (const frame of replay) {
      await probe.evaluate((f) => {
        window.polly167Send(f);
      }, frame);
    }
    await probe.evaluate(
      (frame) => {
        window.polly167Send(frame);
      },
      { type: "STATE_SYNC", key: PLAIN_KEY, value: REMOTE_VALUE, clock: REMOTE_CLOCK } as SyncFrame
    );
    const cValue = await waitFor(
      tabC,
      () => window.pollyE2e167.plain(),
      (v) => v === REMOTE_VALUE,
      "a cold context ended on the stale value: A's frame at the peer's clock won, " +
        "and the peer's real value was then refused by the strictly-greater rule (polly#167)"
    );
    assert(cValue === REMOTE_VALUE, `the cold context settled on ${JSON.stringify(cValue)}`);

    // 4. durable — the half that outlives the tab. Reload reads the value AND
    //    the clock back off IndexedDB; pre-fix it restores A's own value under
    //    the peer's clock, and every later message carrying the peer's value at
    //    that clock is then refused by the strictly-greater rule.
    ctx.log("[e2e] durable: reload A and read what IndexedDB kept");
    await tabA.reload({ waitUntil: "load" });
    await tabA.waitForFunction("window.pollyE2e167 !== undefined", { timeout: 8000 });
    await tabA.evaluate(() => window.pollyE2e167.ready);
    const restored = await tabA.evaluate(() => window.pollyE2e167.note());
    assert(
      restored === REMOTE_VALUE,
      `after a reload A holds ${JSON.stringify(restored)}; the superseded local value ` +
        "was persisted under the peer's clock and came back off the disk (polly#167)"
    );
    ctx.log(`[e2e] durable: A restored ${JSON.stringify(restored)} from IndexedDB`);

    // 5. undisturbed — the guard on cancelling too much.
    ctx.log("[e2e] undisturbed: a debounced write nobody interrupts must still land");
    await tabC.reload({ waitUntil: "load" });
    await tabC.waitForFunction("window.pollyE2e167 !== undefined", { timeout: 8000 });
    await tabC.evaluate(() => window.pollyE2e167.ready);
    const before = (await probe.evaluate(() => window.polly167Frames)).length;
    await tabC.evaluate(() => {
      window.pollyE2e167.setNote("undisturbed");
    });
    await new Promise((r) => setTimeout(r, DEBOUNCE_MS + 400));

    const after = await probe.evaluate(() => window.polly167Frames);
    const sent = after.slice(before).filter((f) => f.value === "undisturbed");
    assert(
      sent.length === 1,
      `an uninterrupted debounced write produced ${sent.length} frames, expected 1`
    );

    await tabC.reload({ waitUntil: "load" });
    await tabC.waitForFunction("window.pollyE2e167 !== undefined", { timeout: 8000 });
    await tabC.evaluate(() => window.pollyE2e167.ready);
    const persisted = await tabC.evaluate(() => window.pollyE2e167.note());
    assert(
      persisted === "undisturbed",
      `an uninterrupted debounced write did not reach storage: reloaded as ${JSON.stringify(persisted)}`
    );
    ctx.log("[e2e] undisturbed: one frame, and it survives a reload");

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
