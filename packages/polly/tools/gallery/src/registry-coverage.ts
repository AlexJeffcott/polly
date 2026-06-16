/**
 * Gallery coverage gap-check.
 *
 * Asserts that every polly-ui component in the generated registry has a section
 * in the gallery. The registry is the source of truth — regenerated whenever a
 * primitive is added (build:registry) — so a new component fails this check
 * until someone writes its specimen. This is what eal's hand-maintained
 * showcase could not give us: no primitive drifts out of the gallery silently.
 *
 * It reads specimens.tsx as TEXT rather than importing it. Importing would pull
 * the entire polly-ui component tree (plus the gallery's stores/actions and
 * their module-level signals) into whatever process runs the check — which, in
 * the shared unit-test runner, perturbs timing-sensitive tests in other files.
 * The `component: "Name"` literal is unique to a section definition (the
 * interface declares `component: string` without quotes, so it never matches),
 * so the text scan is precise. The runtime GALLERY_SECTIONS array is validated
 * end to end by scripts/e2e-gallery.ts, in its own process.
 */

import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { pollyUiComponents } from "../../../src/polly-ui/registry.generated.ts";

const HERE = dirname(fileURLToPath(import.meta.url));
const SPECIMENS_PATH = join(HERE, "specimens.tsx");

export interface CoverageReport {
  /** Component names the registry requires a section for. */
  required: string[];
  /** Component names the gallery sections cover. */
  covered: string[];
  /** Registry components with no section — a coverage GAP (hard failure). */
  missing: string[];
  /** Covered components not in the registry (e.g. Tabs, OverlayRoot). Allowed. */
  extra: string[];
  /** A component covered by more than one section. */
  duplicates: string[];
}

/** The `component: "Name"` value from every section in specimens.tsx. */
function coveredComponents(specimensPath: string): string[] {
  const text = readFileSync(specimensPath, "utf8");
  return [...text.matchAll(/component:\s*"([^"]+)"/g)].map((match) => match[1] ?? "");
}

export function checkGalleryCoverage(specimensPath: string = SPECIMENS_PATH): CoverageReport {
  const required = pollyUiComponents.map((component) => component.name).sort();
  const requiredSet = new Set(required);

  const covered = coveredComponents(specimensPath);
  const coveredSet = new Set(covered);

  const missing = required.filter((name) => !coveredSet.has(name));
  const extra = [...coveredSet].filter((name) => !requiredSet.has(name)).sort();

  const seen = new Set<string>();
  const dupes = new Set<string>();
  for (const name of covered) {
    if (seen.has(name)) dupes.add(name);
    seen.add(name);
  }

  return { required, covered, missing, extra, duplicates: [...dupes].sort() };
}

/** A human-readable one-liner per problem, for CLI / quality-tier output. */
export function formatCoverageProblems(report: CoverageReport): string[] {
  const problems: string[] = [];
  if (report.missing.length > 0) {
    problems.push(
      `${report.missing.length} polly-ui component(s) have no gallery specimen: ${report.missing.join(", ")}. ` +
        "Add a section to tools/gallery/src/specimens.tsx."
    );
  }
  for (const dup of report.duplicates) {
    problems.push(`gallery covers the "${dup}" component in more than one section`);
  }
  return problems;
}

/** Throw if the gallery does not cover every registry component. */
export function assertGalleryCoverage(): void {
  const report = checkGalleryCoverage();
  const problems = formatCoverageProblems(report);
  if (problems.length > 0) {
    throw new Error(`gallery coverage check failed:\n  - ${problems.join("\n  - ")}`);
  }
}
