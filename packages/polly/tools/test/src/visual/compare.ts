/**
 * PNG comparison via pixelmatch.
 *
 * Returns the number of differing pixels and the mismatch ratio against
 * a tolerance. Emits a diff PNG on failure so the author can see which
 * region changed.
 */

import { readFileSync, writeFileSync } from "node:fs";
import pixelmatch from "pixelmatch";
import { PNG } from "pngjs";

export type VisualCompareOptions = {
  /** Pixel-level colour tolerance (0..1). Default 0.1 — per pixel diff threshold. */
  threshold?: number;
  /** Max differing pixels allowed as a ratio of total pixels. Default 0.001. */
  mismatchRatio?: number;
  /** When true, includes anti-aliased pixels in the count. Default false. */
  includeAA?: boolean;
};

export type VisualCompareResult = {
  match: boolean;
  diffPixels: number;
  totalPixels: number;
  ratio: number;
  diffPngPath?: string;
};

export function compareImages(
  baselinePath: string,
  actualPath: string,
  diffPath: string,
  options: VisualCompareOptions = {}
): VisualCompareResult {
  const threshold = options.threshold ?? 0.1;
  const mismatchRatio = options.mismatchRatio ?? 0.001;
  const includeAA = options.includeAA ?? false;

  const baseline = PNG.sync.read(readFileSync(baselinePath));
  const actual = PNG.sync.read(readFileSync(actualPath));

  if (baseline.width !== actual.width || baseline.height !== actual.height) {
    throw new Error(
      `Image dimensions differ: baseline ${baseline.width}x${baseline.height}, actual ${actual.width}x${actual.height}`
    );
  }

  const { width, height } = baseline;
  const diff = new PNG({ width, height });
  const diffPixels = pixelmatch(baseline.data, actual.data, diff.data, width, height, {
    threshold,
    includeAA,
  });

  const totalPixels = width * height;
  const ratio = diffPixels / totalPixels;
  const match = ratio <= mismatchRatio;

  let diffPngPath: string | undefined;
  if (!match) {
    writeFileSync(diffPath, PNG.sync.write(diff));
    diffPngPath = diffPath;
  }

  return { match, diffPixels, totalPixels, ratio, diffPngPath };
}
