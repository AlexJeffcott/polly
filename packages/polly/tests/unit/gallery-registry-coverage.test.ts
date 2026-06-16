/**
 * The gallery's registry gap-check: every polly-ui component in the generated
 * registry must have a section in tools/gallery/src/specimens.tsx. This is the
 * enforcement that keeps the gallery honest — add a primitive without a
 * specimen and this test goes red.
 *
 * The check reads specimens.tsx as text (see registry-coverage.ts) rather than
 * importing it, so this test stays pure node: it pulls in neither the polly-ui
 * component tree nor the gallery's module-level signals, and so cannot perturb
 * other test files. The runtime GALLERY_SECTIONS array is exercised end to end
 * by scripts/e2e-gallery.ts instead.
 */

import { describe, expect, test } from "bun:test";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyUiComponents } from "../../src/polly-ui/registry.generated.ts";
import {
  assertGalleryCoverage,
  checkGalleryCoverage,
  formatCoverageProblems,
} from "../../tools/gallery/src/registry-coverage.ts";

describe("gallery registry coverage", () => {
  test("every registry component has a gallery section", () => {
    // A precise message names the gap if this ever fails.
    expect(checkGalleryCoverage().missing).toEqual([]);
  });

  test("required set equals the generated registry", () => {
    const report = checkGalleryCoverage();
    expect(report.required).toEqual(pollyUiComponents.map((c) => c.name).sort());
    expect(report.required.length).toBeGreaterThan(0);
  });

  test("no component is covered by more than one section", () => {
    expect(checkGalleryCoverage().duplicates).toEqual([]);
  });

  test("assertGalleryCoverage does not throw on the current gallery", () => {
    expect(() => assertGalleryCoverage()).not.toThrow();
  });

  test("extra sections are only known non-registry exports (Tabs, OverlayRoot)", () => {
    // Tabs and OverlayRoot are real polly-ui exports the registry omits; the
    // gallery still covers them. Anything else here is likely a typo'd
    // `component` field that should have matched a registry name.
    expect([...checkGalleryCoverage().extra].sort()).toEqual(["OverlayRoot", "Tabs"]);
  });

  test("a missing section IS reported (the gate has teeth)", () => {
    // Falsification: point the check at a stand-in specimens file covering only
    // one component, and confirm the rest are reported as gaps with a message.
    const dir = mkdtempSync(join(tmpdir(), "gallery-cov-"));
    const stub = join(dir, "specimens.tsx");
    writeFileSync(stub, '{ id: "button", component: "Button", title: "Button" }\n');

    const report = checkGalleryCoverage(stub);
    expect(report.missing.length).toBeGreaterThan(0);
    expect(report.missing).not.toContain("Button");
    const problems = formatCoverageProblems(report);
    expect(problems.length).toBeGreaterThan(0);
    expect(problems[0]).toContain("no gallery specimen");
  });
});
