#!/usr/bin/env bun
/**
 * E2e: every polly-ui control is the height its size token says, and the UA
 * renders its native controls in the page's colour scheme.
 *
 * Why this exists as a browser harness and not a unit test: the defect it
 * guards was invisible to all 1913 unit tests and to 65 committed visual
 * baselines. Control height was derived from font size plus padding
 * rather than read from --polly-control-height-*, so a Button, a TextInput, a
 * Select trigger and a FileInput in one row measured 37.19 / 42 / 40 / 54 px.
 * Nothing asserted they matched, because nothing could: the number only exists
 * once a real engine has done layout.
 *
 * It also pins polly#179 — the UA renders a date picker, a checkbox box and a
 * scrollbar from the `color-scheme` property, not from the palette, so a dark
 * polly page kept light native controls until `color-scheme` was declared.
 *
 * Boots the gallery through serveGallery() — the same code path `polly gallery`
 * runs — so the measurements come from the documented entry point rather than a
 * hand-wired page that could compensate for a gap in the real one.
 */

export const capability = "ui.control-metrics" as const;

import puppeteer, { type Browser } from "puppeteer";
import { serveGallery } from "../tools/gallery/src/server.ts";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

/** The ladder from theme.css, in CSS pixels at a 16px root. */
const LADDER = { sm: 32, md: 40, lg: 48 } as const;

/**
 * Every control the row contract covers, as a selector into the gallery plus
 * the rung it must land on. Selectors match the hashed CSS-module class by
 * prefix, which is stable across builds.
 */
const CONTROLS: Array<{ name: string; selector: string; height: number }> = [
  {
    name: "Button (normal)",
    selector:
      "button[class*=btn_][class*=tierPrimary_]:not([class*=btnSmall_]):not([class*=btnLarge_]):not([class*=btnCircle_])",
    height: LADDER.md,
  },
  {
    name: "Button (small)",
    selector: "button[class*=btn_][class*=btnSmall_]:not([class*=btnCircle_])",
    height: LADDER.sm,
  },
  {
    name: "Button (large)",
    selector: "button[class*=btn_][class*=btnLarge_]:not([class*=btnCircle_])",
    height: LADDER.lg,
  },
  {
    name: "Button (circle)",
    selector: "button[class*=btnCircle_]",
    height: LADDER.md,
  },
  { name: "TextInput", selector: "input[class*=input_][type=text]", height: LADDER.md },
  { name: "Select trigger", selector: "button[class*=trigger_]", height: LADDER.md },
  { name: "FileInput", selector: "label[class*=fileInput_]", height: LADDER.md },
  { name: "Checkbox", selector: "label[class*=checkbox_]", height: LADDER.md },
  { name: "Toggle", selector: "label[class*=toggle_]", height: LADDER.md },
  { name: "Tabs tab", selector: "button[class*=tab_]", height: LADDER.md },
];

/** Controls that must share one corner, so a Button beside a field matches. */
const SHARED_RADIUS: string[] = [
  "button[class*=btn_]:not([class*=btnCircle_])",
  "input[class*=input_][type=text]",
  "button[class*=trigger_]",
  "label[class*=fileInput_]",
];

export async function run(ctx: TierContext): Promise<TierResult> {
  ctx.log("[e2e] serveGallery() — the documented entry point");
  const gallery = await serveGallery({ port: 0 });
  ctx.log(`[e2e] serving at ${gallery.url}`);

  let browser: Browser | undefined;
  try {
    browser = await puppeteer.launch({
      headless: true,
      args: ["--no-sandbox", "--disable-setuid-sandbox"],
    });
    const page = await browser.newPage();
    // 16px root: the ladder is in rem, so a different root would move every
    // expectation together and the assertions below would say nothing.
    await page.setViewport({ width: 1280, height: 1024 });
    await page.goto(gallery.url, { waitUntil: "networkidle0", timeout: 30_000 });
    await page.waitForSelector("#app [data-polly-ui]", { timeout: 15_000 });

    const rootFontSize = await page.evaluate(
      () => getComputedStyle(document.documentElement).fontSize
    );
    assert(
      rootFontSize === "16px",
      `root font-size is ${rootFontSize}, not 16px — the rem ladder below would not resolve to the expected pixels`
    );

    // 1. Every control lands on its rung.
    const measured = await page.evaluate((controls) => {
      return controls.map((c) => {
        const el = document.querySelector(c.selector);
        if (el === null) return { name: c.name, found: false, height: 0, expected: c.height };
        const height = Math.round(el.getBoundingClientRect().height * 100) / 100;
        return { name: c.name, found: true, height, expected: c.height };
      });
    }, CONTROLS);

    const missing = measured.filter((m) => !m.found);
    assert(
      missing.length === 0,
      `no specimen in the gallery for: ${missing.map((m) => m.name).join(", ")} — ` +
        "the selector is stale, or the primitive lost its specimen"
    );

    const offLadder = measured.filter((m) => m.height !== m.expected);
    assert(
      offLadder.length === 0,
      "control height does not match its size token:\n" +
        offLadder.map((m) => `  ${m.name}: ${m.height}px, expected ${m.expected}px`).join("\n")
    );
    for (const m of measured) ctx.log(`[e2e] ${m.name} = ${m.height}px`);

    // 2. A row of mixed controls is one height, which is the point of the
    //    ladder and the thing a per-component assertion cannot state.
    const rowHeights = measured.filter((m) => m.expected === LADDER.md).map((m) => m.height);
    const distinct = [...new Set(rowHeights)];
    assert(
      distinct.length === 1,
      `default-size controls span ${distinct.length} heights (${distinct.join(", ")}px) — they must share one`
    );
    ctx.log(`[e2e] ${rowHeights.length} default-size controls all measure ${distinct[0]}px`);

    // 3. Those controls share one corner.
    const radii = await page.evaluate((selectors) => {
      const out: Array<{ selector: string; radius: string }> = [];
      for (const selector of selectors) {
        const el = document.querySelector(selector);
        if (el !== null) out.push({ selector, radius: getComputedStyle(el).borderRadius });
      }
      return out;
    }, SHARED_RADIUS);
    const distinctRadii = [...new Set(radii.map((r) => r.radius))];
    assert(
      distinctRadii.length === 1,
      "controls do not share one corner:\n" +
        radii.map((r) => `  ${r.selector}: ${r.radius}`).join("\n")
    );
    ctx.log(`[e2e] control radius is ${distinctRadii[0]} everywhere`);

    // 4. color-scheme (polly#179). `normal` means the UA draws its date
    //    pickers, checkbox boxes and scrollbars light whatever the palette says.
    const schemes = await page.evaluate(() => {
      const probe = (theme: string): string => {
        const el = document.createElement("div");
        el.setAttribute("data-polly-theme", theme);
        document.body.appendChild(el);
        const value = getComputedStyle(el).colorScheme;
        el.remove();
        return value;
      };
      return {
        root: getComputedStyle(document.documentElement).colorScheme,
        forcedLight: probe("light"),
        forcedDark: probe("dark"),
      };
    });
    assert(
      schemes.root === "light dark",
      `root color-scheme is "${schemes.root}", expected "light dark" — native controls would not follow the palette`
    );
    assert(
      schemes.forcedLight === "light",
      `[data-polly-theme="light"] color-scheme is "${schemes.forcedLight}", expected "light"`
    );
    assert(
      schemes.forcedDark === "dark",
      `[data-polly-theme="dark"] color-scheme is "${schemes.forcedDark}", expected "dark"`
    );
    ctx.log(
      `[e2e] color-scheme: root "${schemes.root}", forced light "${schemes.forcedLight}", forced dark "${schemes.forcedDark}"`
    );

    ctx.log("[e2e] ui.control-metrics: PASS");
    return { pass: true };
  } finally {
    await browser?.close();
    gallery.stop();
  }
}

if (import.meta.main) await selfRun(capability, run);
