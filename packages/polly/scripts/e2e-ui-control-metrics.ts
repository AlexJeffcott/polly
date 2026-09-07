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

import puppeteer, { type Browser, type Page } from "puppeteer";
import { serveGallery } from "../tools/gallery/src/server.ts";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

/** The ladder from theme.css, in CSS pixels at a 16px root. */
const LADDER = { sm: 32, md: 40, lg: 48 } as const;

/**
 * Every control the row contract covers, as a selector into the gallery plus
 * the rung it must land on. Selectors match the hashed CSS-module class by
 * prefix, which is stable across builds.
 */
const CONTROLS: Array<{ name: string; selector: string; height: number; index?: number }> = [
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
  // 44, not 40: ActionInput's view carries data-polly-interactive, so the
  // hit-target rule in styles.css raises it to the WCAG 2.5.5 target. That
  // floor is deliberate and outranks the ladder. Index 2 is the date
  // specimen — the view is content-sized, so a long label wraps to 78px.
  { name: "ActionInput view", selector: "div[class*=view_]", height: 44, index: 2 },
];

/**
 * Controls that exist only while an overlay is open. Each carries its own
 * border and none is a <Button>, so nothing else in the suite measures them —
 * which is how they all went 2px over when their centring moved from flex to
 * line-height and only Tabs was covered.
 */
// All three carry data-polly-interactive, so styles.css raises them to the
// 44px hit target rather than the 40px control token.
const OVERLAY_CONTROLS: Array<{
  name: string;
  open: string;
  selector: string;
  height: number;
}> = [
  {
    name: "Modal close",
    open: '[data-action="gallery:modal-open"]',
    selector: "[data-polly-modal-content] button[class*=close_]",
    height: 44,
  },
  {
    name: "ConfirmDialog cancel",
    open: '[data-action="gallery:confirm"]',
    selector: "[data-polly-confirm-cancel]",
    height: 44,
  },
  {
    name: "ConfirmDialog confirm",
    open: '[data-action="gallery:confirm"]',
    selector: "[data-polly-confirm-actions] button:not([data-polly-confirm-cancel])",
    height: 44,
  },
];

/**
 * polly#180: the trigger box supplies no layout of its own — the component
 * renders the label/caret row. When `.trigger` lost `display: inline-flex` and
 * only <Select> was updated to compensate, <ActionSelect>'s label and caret
 * became two bare inline boxes and the caret wrapped onto a second line.
 *
 * A short label cannot show that: the trigger sizes to its content, stays under
 * `--polly-control-max-width`, and measures 40px whether or not it has a row.
 * These read the long-label specimens, where the label reaches the cap.
 */
type TriggerCase = {
  name: string;
  selector: string;
  /** Whether this trigger renders a caret. A disabled ActionSelect does not. */
  caret: boolean;
  /** The label is wider than the box, so it must ellipsis-truncate. */
  truncates: boolean;
  /** `.triggerWide`'s floor, where the specimen opts into it. */
  minWidth?: number;
};

const LONG_LABEL_TRIGGERS: TriggerCase[] = [
  {
    name: "Select (long label)",
    selector: "#gallery-select-long button[class*=trigger_]",
    caret: true,
    truncates: true,
  },
  {
    name: "ActionSelect (long label)",
    selector: "#gallery-action-select-long button[class*=trigger_]",
    caret: true,
    truncates: true,
  },
  {
    name: "ActionSelect (long label, disabled)",
    selector: "#gallery-action-select-long-disabled span[class*=trigger_]",
    caret: false,
    truncates: true,
  },
  {
    name: "ActionSelect (long placeholder, empty)",
    selector: "#gallery-action-select-long-empty button[class*=trigger_]",
    caret: true,
    truncates: true,
  },
  {
    // Short label, so nothing truncates: what `wide` must not break is the
    // row itself. --polly-control-min-width-md is 9rem.
    name: "ActionSelect (wide)",
    selector: "#gallery-action-select-wide button[class*=trigger_]",
    caret: true,
    truncates: false,
    minWidth: 144,
  },
];

/** Widths the polly#180 row is measured at. 350 and 900 are the two the
 *  consumer reported the wrapped caret at; 1280 is the suite's own viewport. */
const ROW_VIEWPORT_WIDTHS = [1280, 900, 350] as const;

/** Controls that must share one corner, so a Button beside a field matches. */
const SHARED_RADIUS: string[] = [
  "button[class*=btn_]:not([class*=btnCircle_])",
  "input[class*=input_][type=text]",
  "button[class*=trigger_]",
  "label[class*=fileInput_]",
];

/**
 * How far the caret's vertical centre may sit from the label's and still be on
 * the same row. A wrap moves it by a full line box (~18px at the default font),
 * so anything under a couple of pixels is centring noise, not a second line.
 */
const CARET_CENTRE_TOLERANCE_PX = 2;

/** Two-decimal rounding, so a message reads 210.41px rather than 210.4062. */
function round2(n: number): number {
  return Math.round(n * 100) / 100;
}

/** One trigger as the browser measured it. */
type MeasuredRow = {
  name: string;
  found: true;
  height: number;
  width: number;
  top: number;
  row: { display: string; gap: string } | null;
  label: { centre: number; height: number } | null;
  caret: { centre: number; height: number } | null;
  truncates: boolean;
};

/** The polly#180 assertions for one trigger. Split out for the complexity gate. */
function assertOneRow(
  spec: TriggerCase,
  r: MeasuredRow,
  ctx: TierContext,
  viewportWidth: number
): void {
  const height = round2(r.height);
  assert(
    r.row !== null,
    `${r.name} has no [data-polly-layout] row inside its trigger — .trigger declares no ` +
      "flex or grid of its own, so the component must render the row (polly#180)"
  );
  const display = r.row?.display ?? "";
  assert(
    display === "inline-grid" || display === "grid" || display.includes("flex"),
    `${r.name} row computes display: ${display} — not a flex or grid container`
  );
  assert(
    height === LADDER.md,
    `${r.name} measures ${height}px, expected ${LADDER.md}px — a wrapped caret shows up here`
  );
  assert(r.label !== null, `${r.name} has no [data-polly-select-label] hook`);
  if (spec.truncates) {
    assert(
      r.truncates,
      `${r.name} label does not ellipsis-truncate — it is wider than the control max ` +
        "width, so text-overflow must clip it rather than the row growing or wrapping"
    );
  }
  if (spec.minWidth !== undefined) {
    assert(
      r.width >= spec.minWidth,
      `${r.name} is ${round2(r.width)}px wide, under .triggerWide's ${spec.minWidth}px floor`
    );
  }
  if (spec.caret) {
    assert(r.caret !== null, `${r.name} has no caret`);
    assert(
      r.row?.gap === "8px",
      `${r.name} label/caret gap is ${r.row?.gap}, expected 8px (--polly-space-sm)`
    );
    // Centres, not tops: the caret glyph box is shorter than the text line box,
    // so two items correctly centred on one row have tops a couple of pixels
    // apart. A wrap moves the centre by a whole line box.
    const drift = round2((r.caret?.centre ?? 0) - (r.label?.centre ?? 0));
    assert(
      Math.abs(drift) <= CARET_CENTRE_TOLERANCE_PX,
      `${r.name} caret centre is ${drift}px from its label's — they are on separate lines`
    );
  }
  ctx.log(
    `[e2e] @${viewportWidth}px ${r.name} = ${height}x${round2(r.width)}px, ` +
      `row ${display}, gap ${r.row?.gap ?? "n/a"}`
  );
}

/**
 * polly#180 — the long-label trigger row. Height, one row, a real gap, and an
 * ellipsis instead of a wrap.
 *
 * Extracted from run() only to keep that function under the complexity gate.
 */
async function assertLongLabelRows(
  page: Page,
  ctx: TierContext,
  viewportWidth: number
): Promise<void> {
  const rows = await page.evaluate((triggers) => {
    /** Vertical centre and size of one element, relative to the viewport. */
    const measure = (el: Element | null): { centre: number; height: number } | null => {
      if (el === null) return null;
      const r = el.getBoundingClientRect();
      return { centre: r.top + r.height / 2, height: r.height };
    };
    return triggers.map((t) => {
      const trigger = document.querySelector(t.selector);
      if (trigger === null) return { name: t.name, found: false as const };
      const row = trigger.querySelector("[data-polly-layout]");
      const label = trigger.querySelector<HTMLElement>("[data-polly-select-label]");
      const caret = trigger.querySelector("[class*=caret_]");
      const box = trigger.getBoundingClientRect();
      const rowStyle = row === null ? null : getComputedStyle(row);
      return {
        name: t.name,
        found: true as const,
        height: box.height,
        width: box.width,
        top: box.top,
        row: rowStyle === null ? null : { display: rowStyle.display, gap: rowStyle.columnGap },
        label: measure(label),
        caret: measure(caret),
        // scrollWidth beyond clientWidth is the overflow the ellipsis hides.
        truncates:
          label !== null &&
          label.scrollWidth > label.clientWidth &&
          getComputedStyle(label).textOverflow === "ellipsis",
      };
    });
  }, LONG_LABEL_TRIGGERS);

  for (const [i, r] of rows.entries()) {
    const spec = LONG_LABEL_TRIGGERS[i];
    assert(r.found, `no specimen matched "${spec?.selector}" — ${spec?.name}`);
    if (r.found && spec !== undefined) assertOneRow(spec, r, ctx, viewportWidth);
  }

  // A Select and an ActionSelect carrying the same label are the same box.
  const [selectLong, actionSelectLong] = rows;
  if (selectLong?.found === true && actionSelectLong?.found === true) {
    // Within a pixel: both triggers cap at the same containing block, and
    // shrink-to-fit resolution leaves hundredths of a pixel between them.
    assert(
      Math.abs(selectLong.width - actionSelectLong.width) <= 1 &&
        selectLong.height === actionSelectLong.height,
      "Select and ActionSelect with the same label measure " +
        `${round2(selectLong.width)}x${round2(selectLong.height)} and ` +
        `${round2(actionSelectLong.width)}x${round2(actionSelectLong.height)} — ` +
        "they share one trigger"
    );
    ctx.log(
      `[e2e] @${viewportWidth}px Select and ActionSelect agree at ` +
        `${round2(selectLong.width)}x${round2(selectLong.height)}px`
    );
  }
}

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
        const el = document.querySelectorAll(c.selector)[c.index ?? 0] ?? null;
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

    // 3b. The overlay controls. Open, measure, close.
    for (const control of OVERLAY_CONTROLS) {
      await page.click(control.open);
      await page.waitForSelector(control.selector, { timeout: 5_000 });
      await page.waitForFunction(
        () => document.documentElement.getAttribute("data-polly-scroll-locked") === "true",
        { timeout: 5_000 }
      );
      const height = await page.evaluate((selector) => {
        const el = document.querySelector(selector);
        return el === null ? -1 : Math.round(el.getBoundingClientRect().height * 100) / 100;
      }, control.selector);
      assert(
        height === control.height,
        `${control.name} measures ${height}px, expected ${control.height}px`
      );
      ctx.log(`[e2e] ${control.name} = ${height}px`);
      // Escape reads the overlay stack, and the stack registration happens in
      // the mount effect — press before that and it no-ops against an empty
      // stack. Focus is not the signal here: measured, focus stays on the
      // trigger and never enters the portal. OverlayRoot's scroll lock is,
      // because it is set from the same stack Escape reads.
      await page.waitForFunction(
        () => document.documentElement.getAttribute("data-polly-scroll-locked") === "true",
        { timeout: 5_000 }
      );
      await page.keyboard.press("Escape");
      await page.waitForFunction(
        (selector) => document.querySelector(selector) === null,
        { timeout: 5_000 },
        control.selector
      );
    }

    for (const width of ROW_VIEWPORT_WIDTHS) {
      await page.setViewport({ width, height: 1024 });
      await assertLongLabelRows(page, ctx, width);
    }
    await page.setViewport({ width: 1280, height: 1024 });

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
