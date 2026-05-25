#!/usr/bin/env bun
/**
 * Visual regression runner for the showcase.
 *
 * Bundles src/index.tsx, serves the result on an ephemeral port,
 * launches Puppeteer, navigates to the page, and screenshots each
 * showcase section against its committed baseline.
 *
 * Run from examples/showcase/:
 *
 *   bun tests/visual/run.ts                   # compare against baselines
 *   POLLY_VISUAL_UPDATE=1 bun tests/visual/run.ts   # regenerate baselines
 *
 * Baselines live under tests/visual/__baselines__/, diffs under
 * tests/visual/__diffs__/. Both directories are committed; diffs are
 * .gitignored except as needed.
 */

import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import puppeteer from "puppeteer";
// Importing from source rather than the package export: the bundled
// dist drops the `node:fs` import so `mkdirSync` is undefined at
// runtime. Source-side import sidesteps the bundler issue and is
// fine here since the showcase lives in the same workspace as polly.
import {
  assertSafeUpdateMode,
  isUpdateMode,
  matchBaseline,
  resolveVisualPaths,
} from "../../../../packages/polly/tools/test/src/visual/harness.ts";

assertSafeUpdateMode();

const here = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(here, "../..");
const entry = resolve(projectRoot, "src/index.tsx");
const htmlPath = resolve(projectRoot, "src/index.html");

const SECTIONS = [
  "text",
  "badge",
  "button",
  "link",
  "code",
  "checkbox-toggle",
  "textinput",
  "select-single",
  "select-multi",
  "dropdown",
  "surface",
  "modal",
  "card",
  "cluster-layout",
  "collapsible",
  "skeleton",
];

const build = await Bun.build({
  entrypoints: [entry],
  target: "browser",
  format: "esm",
  minify: false,
  sourcemap: "inline",
});

if (!build.success) {
  process.stderr.write("[visual] build failed:\n");
  for (const log of build.logs) process.stderr.write(`${String(log)}\n`);
  process.exit(1);
}

const jsByPath = new Map<string, string>();
const cssByPath = new Map<string, string>();
for (const out of build.outputs) {
  const text = await out.text();
  if (out.kind === "entry-point" || out.kind === "chunk") {
    jsByPath.set(`/${out.path.replace(/^\.\//, "")}`, text);
  } else if (out.path.endsWith(".css")) {
    cssByPath.set(`/${out.path.replace(/^\.\//, "")}`, text);
  }
}

const entryJsPath = [...jsByPath.keys()].find((p) => p.endsWith("index.js")) ?? "/index.js";
const entryCssPath = [...cssByPath.keys()][0];

const baseHtml = readFileSync(htmlPath, "utf8")
  .replace(/\.\/showcase\.css/g, entryCssPath ?? "/showcase.css")
  .replace(/\.\/index\.tsx/g, entryJsPath);

const server = Bun.serve({
  port: 0,
  fetch(req) {
    const url = new URL(req.url);
    if (url.pathname === "/" || url.pathname === "/index.html") {
      return new Response(baseHtml, { headers: { "Content-Type": "text/html" } });
    }
    const js = jsByPath.get(url.pathname);
    if (js) return new Response(js, { headers: { "Content-Type": "text/javascript" } });
    const css = cssByPath.get(url.pathname);
    if (css) return new Response(css, { headers: { "Content-Type": "text/css" } });
    return new Response("not found", { status: 404 });
  },
});

const url = `http://127.0.0.1:${server.port}/`;
console.log(`[visual] serving ${url}`);

const browser = await puppeteer.launch({
  headless: true,
  args: ["--no-sandbox", "--disable-setuid-sandbox"],
});

const { baselinesDir, diffsDir } = resolveVisualPaths(projectRoot);
let failures = 0;
let passes = 0;

try {
  const page = await browser.newPage();
  await page.setViewport({ width: 1024, height: 768, deviceScaleFactor: 1 });
  await page.goto(url, { waitUntil: "networkidle0" });
  // Wait for the showcase root to render.
  await page.waitForSelector("[data-section='text']", { timeout: 5000 });

  // Each section is captured across the dir × theme matrix so we
  // surface regressions that only appear in one mode (dark-only
  // contrast bug, RTL-only layout flip, etc). Baselines are named
  // `<section>[-rtl][-dark]` so an LTR/light baseline keeps its
  // original short name and the new ones extend it.
  for (const dir of ["ltr", "rtl"] as const) {
    for (const theme of ["light", "dark"] as const) {
      await page.evaluate(
        ({ d, t }) => {
          document.documentElement.setAttribute("dir", d);
          document.documentElement.setAttribute("data-polly-theme", t);
        },
        { d: dir, t: theme },
      );
      await new Promise((r) => setTimeout(r, 50));

      for (const id of SECTIONS) {
        const selector = `[data-section='${id}']`;
        const suffix = `${dir === "rtl" ? "-rtl" : ""}${theme === "dark" ? "-dark" : ""}`;
        const name = `${id}${suffix}`;
        const result = await matchBaseline(page, name, baselinesDir, diffsDir, {
          selector,
          settleMs: 50,
        });
        if (result.passed) {
          console.log(`  ✓ ${name}`);
          passes++;
        } else {
          console.log(`  ✗ ${name} — ${result.reason}`);
          if (result.diffPath) console.log(`    diff: ${result.diffPath}`);
          failures++;
        }
      }
    }
  }
} finally {
  await browser.close();
  server.stop(true);
}

if (isUpdateMode()) {
  console.log(`\n[visual] baselines regenerated (${passes + failures} sections)`);
  process.exit(0);
}

console.log(`\n[visual] ${passes} passed, ${failures} failed`);
process.exit(failures === 0 ? 0 : 1);
