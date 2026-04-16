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
import puppeteer from "puppeteer";
import { signalingServer } from "../../../../src/elysia/signaling-server-plugin";

// ─── Automerge WASM fix ───────────────────────────────────────────────────
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

// ─── Argument parsing ──────────────────────────────────────────────────────

const testDir = resolve(process.cwd(), process.argv[2] ?? "tests/browser");
const filter = process.argv[3] ?? "";
const headless = process.env["HEADLESS"] !== "false";

const glob = new Glob("**/*.browser.ts");
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

// ─── Start server-side infrastructure ──────────────────────────────────────

const signalingPort = 39000 + Math.floor(Math.random() * 1000);
const signalingApp = new Elysia()
  .use(signalingServer({ path: "/polly/signaling" }))
  .listen(signalingPort);
console.log(`[browser-runner] signaling server on ws://127.0.0.1:${signalingPort}/polly/signaling`);

// ─── Launch browser ────────────────────────────────────────────────────────

const browser = await puppeteer.launch({
  headless,
  args: ["--no-sandbox", "--disable-setuid-sandbox"],
});

let totalPassed = 0;
let totalFailed = 0;

for (const testFile of testFiles) {
  const shortName = testFile.replace(`${testDir}/`, "");
  console.log(`\n[browser-runner] running ${shortName}`);

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
    totalFailed += 1;
    continue;
  }

  const jsText = await buildResult.outputs[0]?.text();
  if (!jsText) {
    console.log("  ❌ build produced no output");
    totalFailed += 1;
    continue;
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

  const page = await browser.newPage();
  page.on("console", (msg) => {
    const text = msg.text();
    if (text.includes("[test]")) {
      console.log(`  ${text}`);
    }
  });
  page.on("pageerror", (err: unknown) => {
    const msg = err instanceof Error ? err.message : String(err);
    console.log(`  ❌ page error: ${msg}`);
  });

  await page.goto(`http://127.0.0.1:${server.port}/`, { waitUntil: "domcontentloaded" });

  const timeout = 15_000;
  const deadline = Date.now() + timeout;
  let finished = false;
  while (Date.now() < deadline) {
    finished = await page.evaluate(
      () => (window as unknown as Record<string, unknown>)["__done"] === true
    );
    if (finished) break;
    await new Promise((r) => setTimeout(r, 100));
  }

  if (!finished) {
    console.log(`  ❌ timed out after ${timeout}ms`);
    totalFailed += 1;
    await page.close();
    server.stop();
    continue;
  }

  const results = await page.evaluate(
    () =>
      (window as unknown as Record<string, unknown>)["__testResults"] as unknown as Array<{
        name: string;
        passed: boolean;
        error?: string;
      }>
  );

  for (const r of results ?? []) {
    if (r.passed) {
      console.log(`  ✅ ${r.name}`);
      totalPassed += 1;
    } else {
      console.log(`  ❌ ${r.name}: ${r.error}`);
      totalFailed += 1;
    }
  }

  await page.close();
  server.stop();
}

await browser.close();
(signalingApp as unknown as { server?: { stop?: (f?: boolean) => void } }).server?.stop?.(true);

console.log(`\n[browser-runner] ${totalPassed} passed, ${totalFailed} failed`);
process.exit(totalFailed > 0 ? 1 : 0);
