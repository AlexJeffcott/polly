#!/usr/bin/env bun
/**
 * E2e: the polly-ui component gallery, rendered cold through the real CLI path.
 *
 * Per CLAUDE.md, a green build is not proof a user-facing feature works: the
 * gallery's whole job is to render every primitive in a browser, and that is
 * exactly what unit tests can't see. So this drives the documented entry point —
 * `serveGallery()`, the same code `polly gallery` runs — boots a real Chrome via
 * Puppeteer, and asserts the page actually renders:
 *
 *   1. The overlay hosts the shell mounts are present (OverlayRoot, Toast).
 *   2. Every section in the catalogue has a heading, and the nav lists them all.
 *   3. A substantial number of polly-ui primitives rendered (not a blank page).
 *   4. The console and page are error-free (a broken import or runtime throw
 *      shows up here, not in a unit mock).
 *   5. The interactive path works end to end: the Modal opens on its data-action
 *      click and closes on Escape; an info Toast appears on its click — proving
 *      the action-delegation wiring the gallery boots is live.
 *
 * Then it screenshots the page through @fairfox/polly/test/visual, making the
 * gallery the canonical visual-regression render surface. A missing baseline is
 * written on first run; a committed baseline is diffed (CI refuses update mode).
 * The render assertions above are the machine-independent gate; the pixel
 * baseline is the bonus layer on top.
 */

export const capability = "gallery.render" as const;

import { resolve } from "node:path";
import puppeteer, { type Browser, type ConsoleMessage } from "puppeteer";
import { serveGallery } from "../tools/gallery/src/server.ts";
import { GALLERY_SECTIONS } from "../tools/gallery/src/specimens.tsx";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { matchBaseline, resolveVisualPaths } from "../tools/test/src/visual";

const PROJECT_ROOT = resolve(import.meta.dir, "..");

export async function run(ctx: TierContext): Promise<TierResult> {
  // 1. Start the gallery via the real CLI path (build/serve), random port.
  ctx.log("[e2e] serveGallery() — building and serving the gallery");
  const gallery = await serveGallery({ port: 0 });
  ctx.log(`[e2e] serving at ${gallery.url}`);

  let browser: Browser | undefined;
  try {
    browser = await puppeteer.launch({
      headless: true,
      args: ["--no-sandbox", "--disable-setuid-sandbox"],
    });
    const page = await browser.newPage();
    await page.setViewport({ width: 1280, height: 1024 });

    const consoleErrors: string[] = [];
    const pageErrors: string[] = [];
    page.on("console", (msg: ConsoleMessage) => {
      if (msg.type() === "error") consoleErrors.push(msg.text());
    });
    page.on("pageerror", (err) =>
      pageErrors.push(err instanceof Error ? err.message : String(err))
    );

    await page.goto(gallery.url, { waitUntil: "networkidle0", timeout: 30_000 });
    // The app has rendered once a primitive is in the DOM.
    await page.waitForSelector("#app [data-polly-ui]", { timeout: 15_000 });

    // 2. Overlay hosts the shell mounts.
    assert(
      (await page.$("[data-polly-overlay-root]")) !== null,
      "OverlayRoot did not mount (overlay specimens would have no portal target)"
    );
    assert((await page.$("[data-polly-toast-viewport]")) !== null, "Toast.Viewport did not mount");

    // 3. Every catalogued section has a heading; the nav lists them all.
    for (const section of GALLERY_SECTIONS) {
      assert(
        (await page.$(`#${section.id}`)) !== null,
        `section "${section.id}" (${section.component}) did not render`
      );
    }
    const navLinks = await page.$$eval("nav a", (els) => els.length);
    assert(
      navLinks === GALLERY_SECTIONS.length,
      `nav has ${navLinks} links, expected ${GALLERY_SECTIONS.length} (one per section)`
    );

    // 4. A real page, not a blank one — many primitives rendered.
    const primitiveCount = await page.$$eval("[data-polly-ui]", (els) => els.length);
    assert(
      primitiveCount > 50,
      `only ${primitiveCount} polly-ui elements rendered — the page looks blank/broken`
    );
    ctx.log(
      `[e2e] rendered ${primitiveCount} polly-ui elements across ${GALLERY_SECTIONS.length} sections`
    );

    // 5. Interactive path: Modal opens on data-action, closes on Escape.
    await page.click('[data-action="gallery:modal-open"]');
    await page.waitForSelector("[data-polly-modal-surface]", { timeout: 5_000 });
    // Wait for focus to land inside the dialog. The focus trap and the overlay
    // registration (pushOverlay) both run in the modal's mount effect; once
    // focus is inside, those effects have run, so Escape can reach the overlay
    // stack. Pressing Escape before then would no-op (empty stack) — a race.
    await page.waitForFunction(
      () => document.activeElement?.closest("[data-polly-modal-content]") != null,
      { timeout: 5_000 }
    );
    ctx.log("[e2e] Modal opened via data-action");
    await page.keyboard.press("Escape");
    // waitForFunction (not waitForSelector{hidden}) — unambiguous: poll until the
    // portalled surface is detached from the DOM.
    await page.waitForFunction(
      () => document.querySelector("[data-polly-modal-surface]") === null,
      { timeout: 5_000 }
    );
    ctx.log("[e2e] Modal closed on Escape");

    // Toast appears on its data-action click (action delegation is live).
    await page.click('[data-action="gallery:toast"][data-action-severity="info"]');
    await page.waitForSelector("[data-polly-toast-item]", { timeout: 5_000 });
    ctx.log("[e2e] Toast pushed via data-action");

    // The console/page must be clean. Reported in full so a real error is
    // actionable rather than an opaque count.
    assert(
      pageErrors.length === 0,
      `page emitted ${pageErrors.length} error(s):\n${pageErrors.join("\n")}`
    );
    assert(
      consoleErrors.length === 0,
      `console emitted ${consoleErrors.length} error(s):\n${consoleErrors.join("\n")}`
    );

    // 6. Visual-regression: the gallery is the render surface. Dismiss the toast
    //    first so its auto-dismiss timing can't perturb the pixels, then shoot.
    await page.keyboard.press("Escape");
    const { baselinesDir, diffsDir } = resolveVisualPaths(PROJECT_ROOT);
    // Tolerant on purpose. The render-correctness assertions above are the
    // machine-independent gate; this pixel pass is a coarse "did the whole page
    // break" net. The committed baseline is generated on one OS, so allow a
    // generous mismatch (excluding anti-aliasing) to absorb cross-platform font
    // rendering while still catching a blank/structurally-broken page. Re-baseline
    // on the CI platform with POLLY_VISUAL_UPDATE=1 if the noise floor is higher.
    const visual = await matchBaseline(page, "gallery", baselinesDir, diffsDir, {
      motion: "reduced",
      settleMs: 300,
      includeAA: false,
      mismatchRatio: 0.05,
    });
    if (!visual.passed) {
      return {
        pass: false,
        message: `${visual.reason} (baseline ${visual.baselinePath ?? "?"}, diff ${visual.diffPath ?? "?"})`,
      };
    }
    ctx.log("[e2e] visual baseline matched (or written on first run)");

    ctx.log("[e2e] gallery.render: PASS");
    return { pass: true };
  } finally {
    await browser?.close();
    gallery.stop();
  }
}

if (import.meta.main) await selfRun(capability, run);
