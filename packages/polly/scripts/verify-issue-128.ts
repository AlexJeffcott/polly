// End-to-end verification for issue #128.
//
// <Dropdown> renders its menu with the native Popover API. A shown
// popover is promoted to the browser's top layer, where `position`
// resolves against the viewport rather than the `.dropdown` wrapper —
// so the old `.menu { position: absolute; top: 100%; left: 0 }` rule
// dropped the menu into the viewport's bottom-left corner, off-screen.
//
// The fix pins the menu with `position: fixed` and coordinates measured
// from the trigger inside the popover's `beforetoggle` event, which
// fires synchronously before the popover paints (no flash).
//
// This script renders the *real* <Dropdown> component (the documented
// entry point — not hand-copied markup), bundles it with its CSS
// module, and drives it in a real Chromium via Puppeteer. The top-layer
// containing-block rule only exists in a real browser, so jsdom-style
// unit tests cannot catch this regression.
//
// Each scenario starts from a cold page and asserts the menu lands
// adjacent to its trigger, fully on-screen:
//
//   below        trigger near the top → menu directly below it
//   align-right  align="right"        → menu's right edge meets trigger's
//   narrow       320px viewport       → menu clamped, no horizontal overflow
//   bottom-flip  trigger near bottom  → menu flips above, stays on-screen
//   scroll       page scrolled open   → menu stays pinned to the trigger
//
// The script exits 0 only when every scenario passes.

import { rm, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import puppeteer, { type Browser, type Page } from "puppeteer";

const scriptsDir = import.meta.dir;
const dropdownPath = resolve(scriptsDir, "../src/polly-ui/Dropdown.tsx");
const cssPath = resolve(scriptsDir, "../src/polly-ui/Dropdown.module.css");
const entryPath = resolve(scriptsDir, "__issue-128-entry.tmp.ts");

// Browser-side entry. Renders the real <Dropdown> and exposes a mount
// hook so each scenario can place the trigger and open the menu.
const entrySource = `
import { h, render } from "preact";
import { signal } from "@preact/signals";
import { Dropdown } from ${JSON.stringify(dropdownPath)};
import ${JSON.stringify(cssPath)};

const w = window;

w.__mountDropdown = (opts) => {
  document.body.innerHTML = "";
  document.body.style.margin = "0";
  if (opts.tall) {
    const spacer = document.createElement("div");
    spacer.style.height = "2000px";
    document.body.appendChild(spacer);
  }
  const host = document.createElement("div");
  host.style.position = "absolute";
  host.style.top = opts.triggerTop + "px";
  host.style.left = opts.triggerLeft + "px";
  document.body.appendChild(host);

  const isOpen = signal(false);
  const items = [];
  for (let i = 0; i < opts.itemCount; i++) {
    items.push(h("button", { type: "button", role: "option", key: i }, "Option " + i));
  }
  render(h(Dropdown, { isOpen, trigger: "Open menu", align: opts.align }, items), host);
  w.__open = () => { isOpen.value = true; };
};
`;

type Scenario = {
  name: string;
  viewport: { width: number; height: number };
  mount: {
    triggerTop: number;
    triggerLeft: number;
    align: "left" | "right";
    itemCount: number;
    tall?: boolean;
  };
  scrollY?: number;
};

type Rect = {
  top: number;
  left: number;
  right: number;
  bottom: number;
  width: number;
  height: number;
};

type Measurement = {
  menu: Rect;
  trigger: Rect;
  viewport: { width: number; height: number };
  popoverOpen: boolean;
};

const scenarios: Scenario[] = [
  {
    name: "below",
    viewport: { width: 800, height: 600 },
    mount: { triggerTop: 200, triggerLeft: 48, align: "left", itemCount: 5 },
  },
  {
    name: "align-right",
    viewport: { width: 800, height: 600 },
    mount: { triggerTop: 200, triggerLeft: 600, align: "right", itemCount: 5 },
  },
  {
    name: "narrow",
    viewport: { width: 320, height: 600 },
    mount: { triggerTop: 200, triggerLeft: 200, align: "left", itemCount: 5 },
  },
  {
    name: "bottom-flip",
    viewport: { width: 800, height: 600 },
    mount: { triggerTop: 560, triggerLeft: 48, align: "left", itemCount: 5 },
  },
  {
    name: "scroll",
    viewport: { width: 800, height: 600 },
    mount: { triggerTop: 300, triggerLeft: 48, align: "left", itemCount: 5, tall: true },
    scrollY: 150,
  },
];

// Tolerances. MENU_GAP (4px) + a couple px of sub-pixel rounding.
const MIN_GAP = 2;
const MAX_GAP = 8;
const EDGE = 8;
const ALIGN_TOLERANCE = 1.5;

// The whole menu must sit within the viewport (small sub-pixel slack).
function checkOnScreen(m: Measurement): string[] {
  const { menu, viewport } = m;
  const failures: string[] = [];
  if (menu.top < -1) failures.push(`menu.top ${menu.top.toFixed(0)} above viewport`);
  if (menu.bottom > viewport.height + 1) {
    failures.push(`menu.bottom ${menu.bottom.toFixed(0)} below viewport ${viewport.height}`);
  }
  if (menu.left < EDGE - 1) failures.push(`menu.left ${menu.left.toFixed(0)} past left edge`);
  if (menu.right > viewport.width - EDGE + 1) {
    failures.push(`menu.right ${menu.right.toFixed(0)} past right edge ${viewport.width}`);
  }
  return failures;
}

// Vertical anchoring: directly below the trigger, or flipped above it
// when there is not enough room below (the "bottom-flip" scenario).
function checkVertical(s: Scenario, m: Measurement): string[] {
  const { menu, trigger } = m;
  if (s.name === "bottom-flip") {
    return menu.bottom > trigger.top + 1
      ? [
          `menu.bottom ${menu.bottom.toFixed(0)} should sit above trigger.top ${trigger.top.toFixed(0)}`,
        ]
      : [];
  }
  const gap = menu.top - trigger.bottom;
  return gap < MIN_GAP || gap > MAX_GAP
    ? [`menu-to-trigger gap ${gap.toFixed(1)} outside [${MIN_GAP}, ${MAX_GAP}]`]
    : [];
}

// Horizontal anchoring. Skipped for "narrow", where edge-clamping
// overrides anchoring — the on-screen check already covers it.
function checkHorizontal(s: Scenario, m: Measurement): string[] {
  const { menu, trigger } = m;
  if (s.name === "narrow") return [];
  if (s.name === "align-right") {
    return Math.abs(menu.right - trigger.right) > ALIGN_TOLERANCE
      ? [
          `menu.right ${menu.right.toFixed(0)} not aligned to trigger.right ${trigger.right.toFixed(0)}`,
        ]
      : [];
  }
  return Math.abs(menu.left - trigger.left) > ALIGN_TOLERANCE
    ? [`menu.left ${menu.left.toFixed(0)} not aligned to trigger.left ${trigger.left.toFixed(0)}`]
    : [];
}

function checkScenario(s: Scenario, m: Measurement): string[] {
  const failures = [...checkOnScreen(m), ...checkVertical(s, m), ...checkHorizontal(s, m)];
  if (!m.popoverOpen) failures.push("menu is not :popover-open");
  return failures;
}

// Build the browser bundle (real <Dropdown> + its CSS module) and
// return the JS and CSS to inline. The temp entry is always removed.
async function buildBundle(): Promise<{ js: string; css: string }> {
  await writeFile(entryPath, entrySource);
  try {
    const build = await Bun.build({
      entrypoints: [entryPath],
      target: "browser",
      format: "esm",
      minify: false,
      sourcemap: "none",
    });
    if (!build.success) {
      for (const log of build.logs) console.log(`  ${log}`);
      throw new Error("browser bundle did not build");
    }
    const jsArtifact = build.outputs.find((o) => o.kind === "entry-point");
    const cssArtifact = build.outputs.find((o) => o.path.endsWith(".css"));
    const js = jsArtifact ? await jsArtifact.text() : "";
    const css = cssArtifact ? await cssArtifact.text() : "";
    if (!js) throw new Error("bundle produced no JS");
    if (!css) throw new Error("bundle produced no CSS");
    return { js, css };
  } finally {
    await rm(entryPath, { force: true });
  }
}

// Let the browser settle two animation frames — enough for the scroll
// listener to re-pin the menu after a programmatic scroll.
function flushFrames(page: Page): Promise<void> {
  return page.evaluate(
    () =>
      new Promise<void>((res) => {
        requestAnimationFrame(() => requestAnimationFrame(() => res()));
      })
  );
}

// Mount the Dropdown, open it, then scroll (scroll scenario only).
//
// Preact wires the popover's effects asynchronously, so opening is not
// instantaneous: `__open()` flips the signal, and once the effect runs
// it calls `showPopover()`. Poll for `:popover-open` rather than
// guessing a delay. Positioning itself runs synchronously inside
// `beforetoggle`, before the popover's first paint.
async function mountAndOpen(page: Page, s: Scenario): Promise<void> {
  await page.evaluate((mount) => {
    (window as unknown as { __mountDropdown: (m: unknown) => void }).__mountDropdown(mount);
  }, s.mount);
  await page.evaluate(() => {
    (window as unknown as { __open: () => void }).__open();
  });
  await page.waitForFunction(
    () =>
      document.querySelector("[data-polly-dropdown] [popover]")?.matches(":popover-open") === true,
    { timeout: 5000 }
  );
  if (s.scrollY !== undefined) {
    await page.evaluate((y: number) => {
      window.scrollTo(0, y);
    }, s.scrollY);
    await flushFrames(page);
  }
}

function measure(page: Page): Promise<Measurement> {
  return page.evaluate(() => {
    type Rect = {
      top: number;
      left: number;
      right: number;
      bottom: number;
      width: number;
      height: number;
    };
    const toRect = (el: Element): Rect => {
      const r = el.getBoundingClientRect();
      return {
        top: r.top,
        left: r.left,
        right: r.right,
        bottom: r.bottom,
        width: r.width,
        height: r.height,
      };
    };
    const menu = document.querySelector("[data-polly-dropdown] [popover]");
    const trigger = document.querySelector("[data-polly-dropdown] > button");
    if (!menu || !trigger) throw new Error("dropdown not found in DOM");
    return {
      menu: toRect(menu),
      trigger: toRect(trigger),
      viewport: { width: window.innerWidth, height: window.innerHeight },
      popoverOpen: menu.matches(":popover-open"),
    };
  });
}

function formatRects(m: Measurement): string {
  return (
    `menu{top:${m.menu.top.toFixed(0)} left:${m.menu.left.toFixed(0)} ` +
    `right:${m.menu.right.toFixed(0)} bottom:${m.menu.bottom.toFixed(0)}} ` +
    `trigger{bottom:${m.trigger.bottom.toFixed(0)} left:${m.trigger.left.toFixed(0)} ` +
    `right:${m.trigger.right.toFixed(0)}}`
  );
}

// Run one scenario on a cold page. Returns true when it passes.
async function runScenario(browser: Browser, port: number, s: Scenario): Promise<boolean> {
  const page = await browser.newPage();
  try {
    await page.setViewport(s.viewport);
    await page.goto(`http://127.0.0.1:${port}/`, { waitUntil: "domcontentloaded" });
    await mountAndOpen(page, s);
    const m = await measure(page);
    const failures = checkScenario(s, m);
    const mark = failures.length === 0 ? "PASS" : "FAIL";
    console.log(`▸ ${s.name.padEnd(12)} ${mark}  ${formatRects(m)}`);
    for (const f of failures) console.log(`   ↳ ${f}`);
    return failures.length === 0;
  } finally {
    await page.close();
  }
}

async function main(): Promise<void> {
  const { js, css } = await buildBundle();

  const html = `<!DOCTYPE html>
<html><head><meta charset="utf-8"><style>${css}</style></head>
<body><script type="module">${js}</script></body></html>`;

  const server = Bun.serve({
    port: 0,
    fetch() {
      return new Response(html, { headers: { "Content-Type": "text/html" } });
    },
  });
  const port = server.port;
  if (port === undefined) throw new Error("test server did not bind a port");

  const browser = await puppeteer.launch({
    headless: true,
    args: ["--no-sandbox", "--disable-setuid-sandbox"],
  });

  let allOk = true;
  try {
    for (const s of scenarios) {
      const ok = await runScenario(browser, port, s);
      if (!ok) allOk = false;
    }
  } finally {
    await browser.close();
    server.stop(true);
  }

  console.log();
  if (allOk) {
    console.log("Issue #128 verification PASSED — Dropdown menu anchors to its trigger on-screen.");
    return;
  }
  console.log("Issue #128 verification FAILED.");
  process.exit(1);
}

main().catch((err: unknown) => {
  console.log(`Issue #128 verification FAILED — ${err instanceof Error ? err.message : err}`);
  process.exit(1);
});
