/**
 * Visual regression harness.
 *
 * Runs on the Node side of the Puppeteer browser test runner (not in
 * the browser tab). Takes a full-page or selector-scoped screenshot,
 * compares it against a baseline PNG, writes a diff PNG on mismatch,
 * and returns the result. Set `POLLY_VISUAL_UPDATE=1` to overwrite the
 * baseline instead of comparing — use only locally. CI should refuse
 * that env var and fail on any diff.
 */

import { existsSync, mkdirSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import type { Page } from "puppeteer";
import { compareImages, type VisualCompareOptions, type VisualCompareResult } from "./compare.ts";

export type VisualMatchOptions = VisualCompareOptions & {
  /** CSS selector to scope the screenshot. Defaults to the full page. */
  selector?: string;
  /** Elements matching these selectors are replaced with blanks before capture. */
  maskSelectors?: string[];
  /** Force prefers-color-scheme. Defaults to system. */
  theme?: "light" | "dark";
  /** Force prefers-reduced-motion. Defaults to system. */
  motion?: "full" | "reduced";
  /** Wait this long after setting emulation and before the shot. Default 100ms. */
  settleMs?: number;
};

export type VisualMatchSuccess = {
  name: string;
  passed: true;
  result: VisualCompareResult;
};

export type VisualMatchFailure = {
  name: string;
  passed: false;
  reason: string;
  result?: VisualCompareResult;
  baselinePath: string;
  actualPath: string;
  diffPath?: string;
};

export type VisualMatchResult = VisualMatchSuccess | VisualMatchFailure;

const UPDATE_ENV = "POLLY_VISUAL_UPDATE";
const CI_ENV = "CI";

export function isUpdateMode(): boolean {
  return process.env[UPDATE_ENV] === "1";
}

export function isCi(): boolean {
  return process.env[CI_ENV] === "true" || process.env[CI_ENV] === "1";
}

/** Refuses update mode in CI. Call at the top of a visual test runner. */
export function assertSafeUpdateMode(): void {
  if (isUpdateMode() && isCi()) {
    throw new Error(
      `${UPDATE_ENV}=1 is not allowed in CI. Regenerate baselines locally and commit them.`,
    );
  }
}

function maskInPage(page: Page, selectors: string[]): Promise<void> {
  return page.evaluate((sels) => {
    for (const sel of sels) {
      const nodes = document.querySelectorAll<HTMLElement>(sel);
      for (let i = 0; i < nodes.length; i += 1) {
        const el = nodes[i];
        if (el) el.style.visibility = "hidden";
      }
    }
  }, selectors);
}

async function applyEmulation(page: Page, options: VisualMatchOptions): Promise<void> {
  const features: Array<{ name: string; value: string }> = [];
  if (options.theme) {
    features.push({ name: "prefers-color-scheme", value: options.theme });
  }
  if (options.motion) {
    features.push({
      name: "prefers-reduced-motion",
      value: options.motion === "reduced" ? "reduce" : "no-preference",
    });
  }
  if (features.length > 0) {
    await page.emulateMediaFeatures(features);
  }
}

/**
 * Take a screenshot, compare against the committed baseline, and return
 * a structured result. When the baseline is missing, creates it (in
 * update mode) or fails with a clear message (otherwise).
 */
export async function matchBaseline(
  page: Page,
  name: string,
  baselinesDir: string,
  diffsDir: string,
  options: VisualMatchOptions = {},
): Promise<VisualMatchResult> {
  assertSafeUpdateMode();
  await applyEmulation(page, options);
  if (options.maskSelectors && options.maskSelectors.length > 0) {
    await maskInPage(page, options.maskSelectors);
  }
  if (options.settleMs !== 0) {
    await new Promise((r) => setTimeout(r, options.settleMs ?? 100));
  }

  const safeName = name.replace(/[^a-zA-Z0-9._-]+/g, "_");
  const baselinePath = resolve(baselinesDir, `${safeName}.png`);
  const actualPath = resolve(diffsDir, `${safeName}.actual.png`);
  const diffPath = resolve(diffsDir, `${safeName}.diff.png`);

  mkdirSync(dirname(baselinePath), { recursive: true });
  mkdirSync(dirname(actualPath), { recursive: true });

  const target = options.selector
    ? await page.$(options.selector)
    : null;
  const screenshotBuffer: Buffer = target
    ? Buffer.from(await target.screenshot({ type: "png" }))
    : Buffer.from(await page.screenshot({ type: "png", fullPage: false }));

  writeFileSync(actualPath, screenshotBuffer);

  if (!existsSync(baselinePath) || isUpdateMode()) {
    writeFileSync(baselinePath, screenshotBuffer);
    return {
      name,
      passed: true,
      result: {
        match: true,
        diffPixels: 0,
        totalPixels: 0,
        ratio: 0,
      },
    };
  }

  const result = compareImages(baselinePath, actualPath, diffPath, options);
  if (result.match) {
    return { name, passed: true, result };
  }
  return {
    name,
    passed: false,
    reason: `Visual mismatch: ${result.diffPixels} pixel(s) differ (${(result.ratio * 100).toFixed(3)}%)`,
    result,
    baselinePath,
    actualPath,
    diffPath: result.diffPngPath,
  };
}

export function resolveVisualPaths(projectRoot: string): {
  baselinesDir: string;
  diffsDir: string;
} {
  return {
    baselinesDir: join(projectRoot, "tests/visual/__baselines__"),
    diffsDir: join(projectRoot, "tests/visual/__diffs__"),
  };
}
