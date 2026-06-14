/**
 * @fairfox/polly/test/coverage — the coverage-policy engine.
 *
 * Parses a `bun test --coverage` table and applies a {@link CoverageConfig}.
 * It fails on four conditions, not just low numbers: a non-exempt file below
 * the floor, an exempt key whose source no longer exists, an exemption whose
 * `claimedBy` test no longer exists, and an exempt file that has climbed back
 * over the floor (promote it). It also reports orphans — source files no unit
 * test imports, the blind spot a coverage table can't show.
 *
 * Everything here is parameterised by the project root, so the same engine
 * backs Polly's own gate and the consumer-facing `polly coverage` command.
 */

import { existsSync } from "node:fs";
import { join, resolve } from "node:path";
import { Glob } from "bun";
import type { CoverageConfig } from "./types";

export interface CoverageRow {
  /** Project-relative, e.g. `src/shared/lib/state.ts`. */
  file: string;
  funcs: number;
  lines: number;
}

export interface Violation {
  file: string;
  metric: "lines" | "funcs";
  observed: number;
  required: number;
}

export interface CoverageFindings {
  rowCount: number;
  violations: Violation[];
  staleExempts: string[];
  missingExemptFiles: string[];
  missingClaimedBy: Array<{ file: string; claimedBy: string }>;
  orphans: string[];
  /** True when a floor was configured; false means report-only. */
  enforced: boolean;
}

const DEFAULT_SRC = "src";

/** `../src/foo.ts` (run from a subdir) → `src/foo.ts` (project-relative). */
function normalizePath(raw: string): string {
  return raw.replace(/^(?:\.\.\/)+/, "");
}

/**
 * Parse the `bun test --coverage` table. Only rows under `srcDir` are
 * policy-bearing; the `All files` summary and test-infra rows are skipped.
 * Column order is `File | % Funcs | % Lines | Uncovered`.
 */
export function parseCoverageTable(text: string, srcDir: string): CoverageRow[] {
  const prefix = `${srcDir}/`;
  const rows: CoverageRow[] = [];
  for (const line of text.split("\n")) {
    if (!line.includes("|")) continue;
    if (line.includes("All files") || line.includes("% Funcs")) continue;
    if (line.trim().startsWith("---")) continue;

    const cells = line.split("|").map((c) => c.trim());
    if (cells.length < 3) continue;

    const file = normalizePath(cells[0] ?? "");
    const funcs = Number(cells[1]);
    const lines = Number(cells[2]);
    if (!file.startsWith(prefix) || Number.isNaN(funcs) || Number.isNaN(lines)) continue;

    rows.push({ file, funcs, lines });
  }
  return rows;
}

/** Run `bun test --coverage` in the configured cwd and return combined output. */
export async function runCoverage(root: string, testCwd: string): Promise<string> {
  const proc = Bun.spawn(["bun", "test", "--coverage"], {
    cwd: join(root, testCwd),
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, err] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  if (proc.exitCode !== 0) {
    throw new Error(`bun test --coverage exited ${proc.exitCode}\n${err}`);
  }
  return `${out}\n${err}`;
}

function evaluateRows(
  rows: CoverageRow[],
  config: CoverageConfig
): { violations: Violation[]; staleExempts: string[] } {
  const t = config.defaultThreshold;
  const exempt = config.exempt ?? {};
  const violations: Violation[] = [];
  const staleExempts: string[] = [];
  if (!t) return { violations, staleExempts };

  for (const row of rows) {
    if (exempt[row.file]) {
      if (row.lines >= t.lines && row.funcs >= t.funcs) staleExempts.push(row.file);
      continue;
    }
    if (row.lines < t.lines) {
      violations.push({ file: row.file, metric: "lines", observed: row.lines, required: t.lines });
    }
    if (row.funcs < t.funcs) {
      violations.push({ file: row.file, metric: "funcs", observed: row.funcs, required: t.funcs });
    }
  }
  return { violations, staleExempts };
}

function validateExemptions(
  root: string,
  config: CoverageConfig
): { missingExemptFiles: string[]; missingClaimedBy: Array<{ file: string; claimedBy: string }> } {
  const missingExemptFiles: string[] = [];
  const missingClaimedBy: Array<{ file: string; claimedBy: string }> = [];
  for (const [file, entry] of Object.entries(config.exempt ?? {})) {
    if (!existsSync(resolve(root, file))) missingExemptFiles.push(file);
    const claimedBy = entry.claimedBy.trim();
    if (!claimedBy.startsWith("n/a") && !existsSync(resolve(root, claimedBy))) {
      missingClaimedBy.push({ file, claimedBy });
    }
  }
  return { missingExemptFiles, missingClaimedBy };
}

/** Source files no row covers and no exemption names — the coverage blind spot. */
async function findOrphans(
  root: string,
  srcDir: string,
  covered: Set<string>,
  config: CoverageConfig
): Promise<string[]> {
  const exempt = config.exempt ?? {};
  const orphans: string[] = [];
  const glob = new Glob(`${srcDir}/**/*.{ts,tsx}`);
  for await (const file of glob.scan({ cwd: root, onlyFiles: true })) {
    if (file.endsWith(".d.ts") || /\.test\.tsx?$/.test(file) || file.includes("/__tests__/")) {
      continue;
    }
    if (covered.has(file) || exempt[file]) continue;
    orphans.push(file);
  }
  return orphans.sort();
}

/** Apply the policy to a parsed table. Pure — no spawning. */
export async function evaluateCoverage(
  root: string,
  rows: CoverageRow[],
  config: CoverageConfig
): Promise<CoverageFindings> {
  const srcDir = config.srcDir ?? DEFAULT_SRC;
  const { violations, staleExempts } = evaluateRows(rows, config);
  const { missingExemptFiles, missingClaimedBy } = validateExemptions(root, config);
  const orphans = await findOrphans(root, srcDir, new Set(rows.map((r) => r.file)), config);
  return {
    rowCount: rows.length,
    violations,
    staleExempts,
    missingExemptFiles,
    missingClaimedBy,
    orphans,
    enforced: config.defaultThreshold !== undefined,
  };
}

/** Run the suite under coverage and apply the policy. */
export async function enforceCoverage(
  root: string,
  config: CoverageConfig,
  coverageText?: string
): Promise<CoverageFindings> {
  const srcDir = config.srcDir ?? DEFAULT_SRC;
  const text = coverageText ?? (await runCoverage(root, config.testCwd ?? "."));
  const rows = parseCoverageTable(text, srcDir);
  return evaluateCoverage(root, rows, config);
}

/** True when the findings represent a policy failure (orphans are advisory
 *  unless `strictOrphans`). */
export function hasFailure(findings: CoverageFindings, strictOrphans: boolean): boolean {
  return (
    findings.violations.length > 0 ||
    findings.staleExempts.length > 0 ||
    findings.missingExemptFiles.length > 0 ||
    findings.missingClaimedBy.length > 0 ||
    (strictOrphans && findings.orphans.length > 0)
  );
}
