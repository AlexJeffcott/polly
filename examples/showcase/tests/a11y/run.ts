#!/usr/bin/env bun
/**
 * Accessibility runner for the showcase.
 *
 * Bundles the showcase, serves it, navigates Puppeteer to the page,
 * injects axe-core, and runs an audit scoped to each `[data-section]`.
 * Fails the run if any section reports a violation at impact level
 * `serious` or `critical`.
 *
 * What this catches: labelling, contrast, ARIA misuse, document
 * structure, name/role/value mismatches. What it does NOT catch:
 * keyboard navigation order, focus traps, screen-reader semantics
 * past ARIA, dynamic interaction. Those belong in component-level
 * browser tests.
 *
 * Run from examples/showcase/:
 *
 *   bun tests/a11y/run.ts                # all sections
 *   bun tests/a11y/run.ts button select  # filter by section id
 */

import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import puppeteer, { type Page } from "puppeteer";

const here = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(here, "../..");
const entry = resolve(projectRoot, "src/index.tsx");
const htmlPath = resolve(projectRoot, "src/index.html");
const axeSrcPath = Bun.resolveSync("axe-core/axe.min.js", projectRoot);

const FAIL_IMPACTS = new Set(["serious", "critical"]);

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

const filter = process.argv.slice(2);
const sections = filter.length === 0 ? SECTIONS : SECTIONS.filter((id) => filter.includes(id));

const build = await Bun.build({
  entrypoints: [entry],
  target: "browser",
  format: "esm",
  minify: false,
  sourcemap: "inline",
});

if (!build.success) {
  process.stderr.write("[a11y] build failed:\n");
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
console.log(`[a11y] serving ${url}`);

const axeSource = readFileSync(axeSrcPath, "utf8");

type AxeNode = { html: string; target: string[] };
type AxeViolation = {
  id: string;
  impact: string | null;
  help: string;
  helpUrl: string;
  nodes: AxeNode[];
};
type AxeResults = { violations: AxeViolation[] };

async function runAxe(page: Page, selector: string): Promise<AxeViolation[]> {
  const results = (await page.evaluate(async (sel: string) => {
    // axe-core was injected via addScriptTag; it lives on window.
    const ax = (window as unknown as { axe: { run: (ctx: unknown) => Promise<AxeResults> } }).axe;
    const res = await ax.run({ include: [[sel]] });
    return res;
  }, selector)) as AxeResults;
  return results.violations;
}

const browser = await puppeteer.launch({
  headless: true,
  args: ["--no-sandbox", "--disable-setuid-sandbox"],
});

let totalViolations = 0;
let failingSections = 0;

try {
  const page = await browser.newPage();
  await page.setViewport({ width: 1024, height: 768, deviceScaleFactor: 1 });
  await page.goto(url, { waitUntil: "networkidle0" });
  await page.waitForSelector("[data-section='text']", { timeout: 5000 });
  await page.addScriptTag({ content: axeSource });

  for (const id of sections) {
    const selector = `[data-section='${id}']`;
    const violations = await runAxe(page, selector);
    const blocking = violations.filter((v) => FAIL_IMPACTS.has(v.impact ?? ""));

    if (blocking.length === 0 && violations.length === 0) {
      console.log(`  ✓ ${id}`);
      continue;
    }

    const summary = blocking.length > 0 ? `${blocking.length} blocking` : `${violations.length} info`;
    const status = blocking.length > 0 ? "✗" : "·";
    console.log(`  ${status} ${id} — ${summary}`);

    for (const v of violations) {
      const isBlocking = FAIL_IMPACTS.has(v.impact ?? "");
      const marker = isBlocking ? "    !" : "    -";
      console.log(`${marker} [${v.impact ?? "info"}] ${v.id}: ${v.help}`);
      console.log(`      ${v.helpUrl}`);
      for (const node of v.nodes.slice(0, 3)) {
        console.log(`      at ${node.target.join(" ")}`);
      }
      if (v.nodes.length > 3) {
        console.log(`      …and ${v.nodes.length - 3} more`);
      }
    }

    if (blocking.length > 0) {
      failingSections++;
      totalViolations += blocking.length;
    }
  }
} finally {
  await browser.close();
  server.stop(true);
}

console.log(
  `\n[a11y] ${sections.length - failingSections} sections clean, ${failingSections} failed (${totalViolations} blocking violations)`,
);
process.exit(failingSections === 0 ? 0 : 1);
