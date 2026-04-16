#!/usr/bin/env bun
/**
 * Browser test runner for Polly's browser-only modules.
 *
 * Adapted from lingua's tests/browser/run.ts. Finds all *.browser.ts files
 * in tests/browser/, bundles each with Bun.build, serves the bundle on an
 * ephemeral port, opens a Puppeteer page, and polls window.__done for
 * results. Prints pass/fail per test and exits non-zero if any test failed.
 *
 * Usage:
 *
 *   bun tests/browser/run.ts                    # run all browser tests
 *   bun tests/browser/run.ts mesh-webrtc        # filter by filename
 *   HEADLESS=false bun tests/browser/run.ts     # visible browser
 *
 * The runner also starts any server-side infrastructure the test needs
 * (e.g. a signalling server for WebRTC tests) before launching the
 * browser. Test files declare their server-side needs via a conventional
 * export; see mesh-webrtc.browser.ts for the pattern.
 */

import { type BunPlugin, Glob } from "bun";
import { Elysia } from "elysia";
import puppeteer from "puppeteer";
import { signalingServer } from "../../src/elysia/signaling-server-plugin";

/**
 * Bun bundler plugin that redirects @automerge/automerge to the base64
 * variant. The default browser condition resolves to fullfat_bundler.js
 * which does `import * as wasm from "./automerge_wasm_bg.wasm"` — a
 * static .wasm import that Bun.build can't wire up correctly (the WASM
 * exports resolve to undefined). The base64 variant embeds the WASM as
 * a base64 string and calls initSync() at import time — pure JS, no
 * .wasm file reference, works in any browser without special loader
 * support.
 */
const automergeBase64Path = new URL(
  "../../node_modules/@automerge/automerge/dist/mjs/entrypoints/fullfat_base64.js",
  import.meta.url
).pathname;

const automergeBase64Plugin: BunPlugin = {
  name: "automerge-base64",
  setup(build) {
    build.onResolve({ filter: /^@automerge\/automerge(\/slim)?$/ }, () => {
      return { path: automergeBase64Path };
    });
  },
};

const filter = process.argv[2] ?? "";
const headless = process.env["HEADLESS"] !== "false";
const testDir = import.meta.dir;

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

// Signalling server for WebRTC tests. All browser tests share it.
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

  // Bundle the test file with Bun.build. The output is a single ESM chunk
  // that includes the harness, the Polly modules under test, and tweetnacl.
  // External deps that don't exist in browsers (Node builtins, ws, etc.)
  // are excluded; the test file must not import them.
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
    console.log(`  ❌ build failed:`);
    for (const log of buildResult.logs) {
      console.log(`     ${log}`);
    }
    totalFailed += 1;
    continue;
  }

  const jsText = await buildResult.outputs[0]?.text();
  if (!jsText) {
    console.log(`  ❌ build produced no output`);
    totalFailed += 1;
    continue;
  }

  // Serve the bundle on an ephemeral port.
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

  // Poll for completion. The harness sets window.__done = true when all
  // tests have run.
  const timeout = 15_000;
  const deadline = Date.now() + timeout;
  let finished = false;
  while (Date.now() < deadline) {
    finished = await page.evaluate(
      () => (window as unknown as Record<string, unknown>).__done === true
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

  // Collect results.
  const results = await page.evaluate(
    () =>
      (window as unknown as Record<string, unknown>).__testResults as Array<{
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
