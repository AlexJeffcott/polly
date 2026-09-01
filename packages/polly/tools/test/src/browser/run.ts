#!/usr/bin/env bun

/**
 * Browser test runner for Polly applications.
 *
 * Finds all *.browser.ts files in a given directory, bundles each with
 * Bun.build for the browser target (with an internal Automerge WASM fix),
 * serves the bundle on an ephemeral port, and opens a Puppeteer page in its
 * own browser context. The page pushes its results back through bindings the
 * runner exposes (`__pollyReport` for the final tally, `__pollyProgress` per
 * test). Prints pass/fail per test and exits non-zero if any test failed.
 *
 * A file that stops reporting is diagnosed rather than merely timed out: the
 * runner asks the page whether its main thread is still free, so a runaway
 * loop in the code under test reads differently from a suite that never
 * finished, and the tests that never ran are counted (polly#177). Set
 * POLLY_BROWSER_STACK=1 to also print the stack a wedged page is executing.
 *
 * A signalling server for WebRTC tests starts automatically on a random
 * port. The URL is injected into the bundle via process.env.SIGNALING_URL.
 *
 * Usage (from project root):
 *
 *   bun tools/test/src/browser/run.ts [testDir] [filter]
 *
 * Examples:
 *
 *   bun tools/test/src/browser/run.ts tests/browser
 *   bun tools/test/src/browser/run.ts tests/browser mesh-webrtc
 *   HEADLESS=false bun tools/test/src/browser/run.ts tests/browser
 *
 * When invoked without a testDir, defaults to tests/browser relative to cwd.
 */

import { resolve } from "node:path";
import { type BunPlugin, Glob } from "bun";
import { Elysia } from "elysia";
import puppeteer, { type Browser, type CDPSession, type Page } from "puppeteer";
import { signalingServer } from "../../../../src/elysia/signaling-server-plugin";
import { resolveListenPort } from "../e2e-shared/ephemeral-port";
import {
  applyProgress,
  emptyProgress,
  errMessage,
  type FileTally,
  type ProgressEvent,
  runSuite,
  type StallState,
  type SuiteProgress,
  summariseTimeout,
  type TestResult,
} from "./runner-core";
import { createSourceMapLookup, type SourceMapLookup } from "./source-map";

// Automerge WASM fix
// Bun.build's target: "browser" picks Automerge's fullfat_bundler.js which
// does a static .wasm import that Bun can't wire up. Redirect to the
// base64 variant which embeds the WASM as a string and self-initialises.

// Resolve Automerge relative to polly's own install, not the runner's CWD.
// `dist/mjs/entrypoints/fullfat_base64.js` is not in the package's `exports`
// map, so it cannot be resolved by subpath — resolve the package entry and
// derive the root. A CWD-relative path silently failed to exist when the
// dependency was hoisted differently in a consumer monorepo (polly#159).
const automergeMarker = "@automerge/automerge";
const automergeEntry = Bun.resolveSync(automergeMarker, import.meta.dir);
const automergeBase64Path = resolve(
  automergeEntry.slice(0, automergeEntry.lastIndexOf(automergeMarker) + automergeMarker.length),
  "dist/mjs/entrypoints/fullfat_base64.js"
);

const automergeBase64Plugin: BunPlugin = {
  name: "automerge-base64",
  setup(build) {
    build.onResolve({ filter: /^@automerge\/automerge(\/slim)?$/ }, () => {
      return { path: automergeBase64Path };
    });
  },
};

// Argument parsing

const testDir = resolve(process.cwd(), process.argv[2] ?? "tests/browser");
const filter = process.argv[3] ?? "";
const headless = process.env["HEADLESS"] !== "false";

const glob = new Glob("**/*.browser.{ts,tsx}");
const testFiles: string[] = [];
for await (const file of glob.scan({ cwd: testDir, absolute: true })) {
  if (file.includes("harness")) continue;
  if (filter && !file.includes(filter)) continue;
  testFiles.push(file);
}

if (testFiles.length === 0) {
  console.log(`[browser-runner] no test files found${filter ? ` matching "${filter}"` : ""}`);
  process.exit(0);
}

console.log(`[browser-runner] found ${testFiles.length} test file(s)`);

// Start server-side infrastructure

// Port 0: the kernel assigns a free port and the server owns it from that
// moment, so a second runner on the same machine cannot collide (polly#174).
const signalingApp = new Elysia().use(signalingServer({ path: "/polly/signaling" })).listen(0);
const signalingPort = resolveListenPort(signalingApp);
console.log(`[browser-runner] signaling server on ws://127.0.0.1:${signalingPort}/polly/signaling`);

// Launch browser
//
// No `protocolTimeout` override: results arrive via `page.exposeFunction`
// (a push from the page over CDP `Runtime.bindingCalled` events), not via
// polled `page.evaluate` calls. Without a long-running `Runtime.callFunctionOn`
// on the hot path there is no protocol round-trip for a busy renderer to
// stall, so the timeout the previous polling design had to guard against
// is no longer reachable (polly#138).

const launchArgs = ["--no-sandbox", "--disable-setuid-sandbox"];

let browser: Browser = await puppeteer.launch({ headless, args: launchArgs });

/** How long to wait for a page to answer before calling it wedged. */
const PROBE_TIMEOUT_MS = 2_000;
/** How long to wait for a paused stack when POLLY_BROWSER_STACK is set. */
const PAUSE_TIMEOUT_MS = 8_000;
/** How long teardown of one file's context may take before it is abandoned. */
const CLOSE_TIMEOUT_MS = 5_000;

/** Set POLLY_BROWSER_STACK=1 to capture the JS stack of a wedged page. */
const captureStacks = process.env["POLLY_BROWSER_STACK"] === "1";

/** Marks the per-file deadline so a real page error still propagates. */
class FileTimeout extends Error {}

/** Await `task`, giving up after `ms`. Never rejects. */
async function withDeadline(task: Promise<unknown>, ms: number): Promise<void> {
  let timer: ReturnType<typeof setTimeout> | undefined;
  const deadline = new Promise<void>((r) => {
    timer = setTimeout(r, ms);
  });
  try {
    await Promise.race([task.then(noop, noop), deadline]);
  } finally {
    if (timer) clearTimeout(timer);
  }
}

function noop(): void {
  /* a settled task's value and error are both uninteresting here */
}

/**
 * The browser for the next file, relaunched if the connection has gone.
 *
 * A file whose page wedged used to be able to take the whole browser with
 * it, and every later file then failed with `Connection closed.` — one
 * stall turning five healthy files into five failures (polly#177). Each
 * file now checks the connection first, so a dead browser costs one
 * relaunch instead of the rest of the run.
 */
async function ensureBrowser(): Promise<Browser> {
  if (browser.connected) return browser;
  console.log("[browser-runner] browser connection lost — relaunching");
  browser = await puppeteer.launch({ headless, args: launchArgs });
  return browser;
}

/**
 * Ask the page a trivial question to find out whether its main thread is
 * free. A page in a runaway loop never runs the task, so the call never
 * returns; that silence is the reading.
 */
async function probeStallState(page: Page): Promise<StallState> {
  if (page.isClosed() || !browser.connected) return "unknown";
  let timer: ReturnType<typeof setTimeout> | undefined;
  const deadline = new Promise<boolean>((r) => {
    timer = setTimeout(() => r(false), PROBE_TIMEOUT_MS);
  });
  try {
    const answered = await Promise.race([
      page
        .evaluate(() => true)
        .then(
          () => true,
          () => false
        ),
      deadline,
    ]);
    return answered ? "idle" : "looping";
  } finally {
    if (timer) clearTimeout(timer);
  }
}

/**
 * Present a mapped `path:line:column` relative to the working directory.
 *
 * A bundle's `sources` are relative to the runner's cwd, which for a file
 * outside the package reads as a long climb of `../` segments. Resolve it,
 * then show the shorter of the two forms.
 */
function presentPosition(position: string): string {
  const lastColon = position.lastIndexOf(":");
  const fileEnd = lastColon === -1 ? -1 : position.lastIndexOf(":", lastColon - 1);
  if (fileEnd === -1) return position;
  const absolute = resolve(process.cwd(), position.slice(0, fileEnd));
  const prefix = `${process.cwd()}/`;
  const shown = absolute.startsWith(prefix) ? absolute.slice(prefix.length) : absolute;
  return `${shown}${position.slice(fileEnd)}`;
}

/**
 * Interrupt a wedged page and print where its JavaScript is.
 *
 * `Debugger.enable` is itself dispatched to the main thread, so it cannot be
 * sent once that thread is spinning — the domain has to be live before the
 * page starts work. That costs V8 some optimisation on every run, so it is
 * opt-in via POLLY_BROWSER_STACK=1 and the timeout message points at it.
 */
async function printPausedStack(debug: DebugAttachment): Promise<void> {
  const session = debug.session;
  if (!session) return;
  await session.send("Debugger.pause").catch(noop);
  const deadline = Date.now() + PAUSE_TIMEOUT_MS;
  while (Date.now() < deadline && !debug.frames()) {
    await new Promise((r) => setTimeout(r, 100));
  }
  const frames = debug.frames();
  if (!frames) {
    console.log("     (the page could not be paused — no stack available)");
    return;
  }
  console.log("     the page was executing:");
  for (const frame of frames.callFrames.slice(0, 12)) {
    const { lineNumber, columnNumber } = frame.location;
    const column = columnNumber ?? 0;
    const original = debug.resolve(lineNumber, column);
    const where = original
      ? presentPosition(original)
      : `${frame.url || "(inline)"}:${lineNumber + 1}:${column}`;
    console.log(`       ${frame.functionName || "(anonymous)"} @ ${where}`);
  }
}

interface PausedFrames {
  callFrames: Array<{
    functionName: string;
    url: string;
    location: { lineNumber: number; columnNumber?: number };
  }>;
}

/** A live debugger attachment, present only under POLLY_BROWSER_STACK=1. */
interface DebugAttachment {
  session?: CDPSession;
  frames: () => PausedFrames | undefined;
  /** Generated document position → the author's own source, when mappable. */
  resolve: (line: number, column: number) => string | undefined;
}

/**
 * Report a file that ran out of time: what the page was doing, how far the
 * suite got, and how many of its tests never finished.
 */
async function reportTimeout(
  page: Page,
  progress: SuiteProgress,
  timeoutMs: number,
  debug: DebugAttachment
): Promise<FileTally> {
  // Read the page's state before tearing it down: what the renderer was doing
  // decides whether this is a runaway loop in the code under test or a suite
  // that simply never finished (polly#177).
  const state = await probeStallState(page);
  const { tally, lines } = summariseTimeout(progress, timeoutMs, state);
  for (const line of lines) console.log(line);
  if (state !== "looping") return tally;
  if (debug.session) {
    await printPausedStack(debug);
  } else {
    console.log("     re-run with POLLY_BROWSER_STACK=1 to print the running stack");
  }
  return tally;
}

/** Print one file's finished results and tally them. */
function printResults(results: TestResult[]): FileTally {
  let passed = 0;
  let failed = 0;
  for (const r of results) {
    if (r.passed) {
      console.log(`  ✅ ${r.name}`);
      passed += 1;
    } else {
      console.log(`  ❌ ${r.name}: ${r.error}`);
      failed += 1;
    }
  }
  return { passed, failed };
}

/**
 * Build, serve, and run one test file in its own browser context. Returns
 * its pass/fail tally. Build failures and per-file timeouts are reported
 * here (not thrown); a page-level uncaught error propagates so the suite
 * records the file as failed. The context and server are always cleaned up
 * first, under a deadline so a wedged renderer cannot stall teardown.
 */
/** The bundle for one test file, wrapped in the document that serves it. */
interface BuiltPage {
  jsText: string;
  html: string;
  /** Lines of wrapper above the bundle, so debugger positions can be mapped. */
  bundleLineOffset: number;
}

/**
 * Bundle one test file for the browser. Reports its own failures and returns
 * undefined, so the caller has nothing to decide.
 */
async function buildPage(testFile: string): Promise<BuiltPage | undefined> {
  const buildResult = await Bun.build({
    entrypoints: [testFile],
    target: "browser",
    format: "esm",
    minify: false,
    sourcemap: "inline",
    plugins: [automergeBase64Plugin],
    define: {
      "process.env.SIGNALING_URL": JSON.stringify(
        `ws://127.0.0.1:${signalingPort}/polly/signaling`
      ),
    },
  });

  if (!buildResult.success) {
    console.log("  ❌ build failed:");
    for (const log of buildResult.logs) {
      console.log(`     ${log}`);
    }
    return undefined;
  }

  const jsText = await buildResult.outputs[0]?.text();
  if (!jsText) {
    console.log("  ❌ build produced no output");
    return undefined;
  }

  // The bundle starts on its own line so a debugger position in the document
  // maps to the bundle by subtracting a fixed line count, with no column
  // adjustment (polly#177). Keep the newline after the opening tag.
  const htmlPrefix = `<!DOCTYPE html>
<html><head><meta charset="utf-8"></head>
<body>
<script type="module">
`;
  return {
    jsText,
    html: `${htmlPrefix}${jsText}\n</script>\n</body></html>`,
    bundleLineOffset: htmlPrefix.split("\n").length - 1,
  };
}

async function runFile(testFile: string): Promise<FileTally> {
  const built = await buildPage(testFile);
  if (!built) return { passed: 0, failed: 1 };
  const { jsText, html, bundleLineOffset } = built;

  const server = Bun.serve({
    port: 0,
    fetch() {
      return new Response(html, { headers: { "Content-Type": "text/html" } });
    },
  });

  // One context per file. Closing it is a browser-process operation, so a
  // renderer that refuses to yield is still torn down, and nothing a file
  // leaves behind can reach the next one (polly#177).
  const context = await (await ensureBrowser()).createBrowserContext();

  let page: Page | undefined;
  try {
    const newPage = await context.newPage();
    page = newPage;
    newPage.on("console", (msg) => {
      const text = msg.text();
      if (text.includes("[test]")) {
        console.log(`  ${text}`);
      }
    });

    // Push-based reporting (polly#138): the page calls back into Node via
    // `__pollyReport(results)` when its in-page suite has finished.
    let reportResolve!: (results: TestResult[]) => void;
    let reportReject!: (err: Error) => void;
    const outcome = new Promise<TestResult[]>((resolve, reject) => {
      reportResolve = resolve;
      reportReject = reject;
    });

    // Wire the report channel BEFORE navigating. `exposeFunction` is async;
    // if the page were allowed to load first it could call `__pollyReport`
    // before the binding existed, and the result would be lost forever —
    // the deadlock seen when the runner's CWD was outside the test package
    // (polly#159).
    await newPage.exposeFunction("__pollyReport", (results: TestResult[]) => {
      reportResolve(results);
    });

    // The progress channel carries per-test events as the file runs, so a
    // page that stops part-way still leaves a record of how far it got.
    const progress = emptyProgress();
    await newPage.exposeFunction("__pollyProgress", (event: ProgressEvent) => {
      applyProgress(progress, event);
    });

    newPage.on("pageerror", (err: unknown) => {
      reportReject(err instanceof Error ? err : new Error(errMessage(err)));
    });

    let pausedFrames: PausedFrames | undefined;
    let debugSession: CDPSession | undefined;
    // Built once and only when a stack is actually printed: decoding a
    // bundle's mappings is wasted work on a healthy run.
    let lookup: SourceMapLookup | undefined;
    let lookupBuilt = false;
    const resolvePosition = (line: number, column: number): string | undefined => {
      if (!lookupBuilt) {
        lookup = createSourceMapLookup(jsText, bundleLineOffset);
        lookupBuilt = true;
      }
      return lookup?.(line, column);
    };
    if (captureStacks) {
      debugSession = await newPage.createCDPSession();
      debugSession.on("Debugger.paused", (event) => {
        pausedFrames = event as unknown as PausedFrames;
      });
      await debugSession.send("Debugger.enable");
    }

    // Bound the wait so a page that never reports (a swallowed error, a hung
    // renderer) fails the file instead of hanging the whole suite forever
    // (polly#159). Override via POLLY_BROWSER_TIMEOUT_MS.
    const timeoutMs = Number(process.env["POLLY_BROWSER_TIMEOUT_MS"] ?? 60000);

    // A file whose module scope loops never reaches DOMContentLoaded, so it
    // stalls in `goto` rather than in the wait below. Puppeteer's own
    // navigation timeout would report that as "Navigation timeout of 30000ms
    // exceeded" — the same silence polly#177 started from. Hold navigation to
    // the file's own deadline and diagnose it the same way.
    newPage.setDefaultNavigationTimeout(timeoutMs);
    const debug: DebugAttachment = {
      session: debugSession,
      frames: () => pausedFrames,
      resolve: resolvePosition,
    };
    try {
      await newPage.goto(`http://127.0.0.1:${server.port}/`, { waitUntil: "domcontentloaded" });
    } catch (err) {
      if (!(err instanceof Error) || err.name !== "TimeoutError") throw err;
      return await reportTimeout(newPage, progress, timeoutMs, debug);
    }

    let timeoutTimer: ReturnType<typeof setTimeout> | undefined;
    const timeout = new Promise<never>((_, reject) => {
      timeoutTimer = setTimeout(() => reject(new FileTimeout()), timeoutMs);
    });

    let results: TestResult[];
    try {
      results = await Promise.race([outcome, timeout]);
    } catch (err) {
      if (!(err instanceof FileTimeout)) throw err;
      return await reportTimeout(newPage, progress, timeoutMs, debug);
    } finally {
      if (timeoutTimer) clearTimeout(timeoutTimer);
    }

    return printResults(results);
  } finally {
    // Under a deadline: a page whose main thread never yields can leave both
    // of these pending, and teardown must not become the new hang.
    if (page) await withDeadline(page.close(), CLOSE_TIMEOUT_MS);
    await withDeadline(context.close(), CLOSE_TIMEOUT_MS);
    server.stop();
  }
}

const { passed: totalPassed, failed: totalFailed } = await runSuite(testFiles, runFile, {
  label: (testFile) => testFile.replace(`${testDir}/`, ""),
});

await browser.close();
(signalingApp as unknown as { server?: { stop?: (f?: boolean) => void } }).server?.stop?.(true);

console.log(`\n[browser-runner] ${totalPassed} passed, ${totalFailed} failed`);
process.exit(totalFailed > 0 ? 1 : 0);
