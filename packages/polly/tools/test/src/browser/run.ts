#!/usr/bin/env bun

/**
 * Browser test runner for Polly applications.
 *
 * Finds all *.browser.ts files in a given directory, bundles each with
 * Bun.build for the browser target (with an internal Automerge WASM fix),
 * serves the bundle on an ephemeral port, opens a Puppeteer page, and
 * polls window.__done for results. Prints pass/fail per test and exits
 * non-zero if any test failed.
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
import puppeteer, { type Page } from "puppeteer";
import { signalingServer } from "../../../../src/elysia/signaling-server-plugin";
import { errMessage, type FileTally, runSuite } from "./runner-core";

// Automerge WASM fix
// Bun.build's target: "browser" picks Automerge's fullfat_bundler.js which
// does a static .wasm import that Bun can't wire up. Redirect to the
// base64 variant which embeds the WASM as a string and self-initialises.

const automergeBase64Path = resolve(
  process.cwd(),
  "node_modules/@automerge/automerge/dist/mjs/entrypoints/fullfat_base64.js"
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

const signalingPort = 39000 + Math.floor(Math.random() * 1000);
const signalingApp = new Elysia()
  .use(signalingServer({ path: "/polly/signaling" }))
  .listen(signalingPort);
console.log(`[browser-runner] signaling server on ws://127.0.0.1:${signalingPort}/polly/signaling`);

// Launch browser
//
// No `protocolTimeout` override: results arrive via `page.exposeFunction`
// (a push from the page over CDP `Runtime.bindingCalled` events), not via
// polled `page.evaluate` calls. Without a long-running `Runtime.callFunctionOn`
// on the hot path there is no protocol round-trip for a busy renderer to
// stall, so the timeout the previous polling design had to guard against
// is no longer reachable (polly#138).

const browser = await puppeteer.launch({
  headless,
  args: ["--no-sandbox", "--disable-setuid-sandbox"],
});

/**
 * Build, serve, and run one test file on a fresh page. Returns its
 * pass/fail tally. Build failures are reported here (not thrown);
 * a page-level uncaught error propagates so the suite records the
 * file as failed. The page and server are always cleaned up first.
 */
interface TestResult {
  name: string;
  passed: boolean;
  error?: string;
}
async function runFile(testFile: string): Promise<FileTally> {
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
    return { passed: 0, failed: 1 };
  }

  const jsText = await buildResult.outputs[0]?.text();
  if (!jsText) {
    console.log("  ❌ build produced no output");
    return { passed: 0, failed: 1 };
  }

  const html = `<!DOCTYPE html>
<html><head><meta charset="utf-8"></head>
<body>
<script type="module">${jsText}</script>
</body></html>`;

  const server = Bun.serve({
    port: 0,
    fetch() {
      return new Response(html, { headers: { "Content-Type": "text/html" } });
    },
  });

  let page: Page | undefined;
  try {
    const newPage = await browser.newPage();
    page = newPage;
    newPage.on("console", (msg) => {
      const text = msg.text();
      if (text.includes("[test]")) {
        console.log(`  ${text}`);
      }
    });

    // Push-based reporting (polly#138): the page calls back into Node via
    // `__pollyReport(results)` when its in-page suite has finished. We
    // bind that function and the page-error channel to a single Promise
    // before navigating, then `await` it — no `page.evaluate` polling
    // and no CDP timeout for a busy renderer to trip.
    const outcome = new Promise<TestResult[]>((resolve, reject) => {
      newPage
        .exposeFunction("__pollyReport", (results: TestResult[]) => {
          resolve(results);
        })
        .catch(reject);
      newPage.on("pageerror", (err: unknown) => {
        reject(err instanceof Error ? err : new Error(errMessage(err)));
      });
    });

    await newPage.goto(`http://127.0.0.1:${server.port}/`, { waitUntil: "domcontentloaded" });

    const results = await outcome;

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
  } finally {
    if (page) {
      await page.close().catch(() => {
        // ignore — page may already be gone after an uncaught error
      });
    }
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
