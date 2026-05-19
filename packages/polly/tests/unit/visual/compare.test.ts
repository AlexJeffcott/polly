import { beforeEach, expect, test } from "bun:test";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { PNG } from "pngjs";
import { compareImages } from "../../../tools/test/src/visual/compare";

let root: string;

beforeEach(() => {
  root = mkdtempSync(join(tmpdir(), "polly-visual-"));
});

function writePng(path: string, fill: [number, number, number, number], w = 16, h = 16): void {
  const png = new PNG({ width: w, height: h });
  for (let y = 0; y < h; y += 1) {
    for (let x = 0; x < w; x += 1) {
      const idx = (y * w + x) * 4;
      png.data[idx] = fill[0];
      png.data[idx + 1] = fill[1];
      png.data[idx + 2] = fill[2];
      png.data[idx + 3] = fill[3];
    }
  }
  writeFileSync(path, PNG.sync.write(png));
}

test("identical images match with zero diff pixels", () => {
  const a = join(root, "a.png");
  const b = join(root, "b.png");
  const diff = join(root, "diff.png");
  writePng(a, [255, 255, 255, 255]);
  writePng(b, [255, 255, 255, 255]);
  const r = compareImages(a, b, diff);
  expect(r.match).toBe(true);
  expect(r.diffPixels).toBe(0);
});

test("completely different images fail and emit a diff PNG", () => {
  const a = join(root, "a.png");
  const b = join(root, "b.png");
  const diff = join(root, "diff.png");
  writePng(a, [0, 0, 0, 255]);
  writePng(b, [255, 255, 255, 255]);
  const r = compareImages(a, b, diff);
  expect(r.match).toBe(false);
  expect(r.diffPixels).toBeGreaterThan(0);
  expect(r.diffPngPath).toBe(diff);
});

test("mismatchRatio tolerates small differences", () => {
  const a = join(root, "a.png");
  const b = join(root, "b.png");
  const diff = join(root, "diff.png");
  writePng(a, [100, 100, 100, 255]);
  const png = PNG.sync.read(readFileSync(a));
  png.data[0] = 255;
  writeFileSync(b, PNG.sync.write(png));
  const permissive = compareImages(a, b, diff, {
    threshold: 0.1,
    mismatchRatio: 0.01,
  });
  expect(permissive.match).toBe(true);
  const strict = compareImages(a, b, diff, {
    threshold: 0.1,
    mismatchRatio: 0,
  });
  expect(strict.match).toBe(false);
});

test("mismatched image dimensions throw", () => {
  const a = join(root, "a.png");
  const b = join(root, "b.png");
  const diff = join(root, "diff.png");
  writePng(a, [0, 0, 0, 255], 16, 16);
  writePng(b, [0, 0, 0, 255], 32, 32);
  expect(() => compareImages(a, b, diff)).toThrow(/dimensions/);
});
