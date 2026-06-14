#!/usr/bin/env bun

/**
 * Coverage-policy enforcer. Applies the per-file rules in
 * `scripts/coverage.config.ts` to a `bun test --coverage` table and exits
 * non-zero when the policy is violated.
 *
 * It fails on FOUR conditions, not just low numbers:
 *
 *   1. violations          a non-exempt source file is below the floor
 *   2. missingExemptFiles   an exempt key no longer exists on disk (renamed?)
 *   3. missingClaimedBy     an exemption's `claimedBy` test doesn't exist
 *   4. staleExempts         an exempt file climbed past the floor — promote it
 *
 * (2)–(4) are the point: a coverage gate that only checks numbers lets the
 * exemption list rot into a pile of lies. Validating that every "covered
 * elsewhere" claim still points at a real test is what makes the tiering
 * legible — and is the cheapest guard against the polly#57 failure mode where
 * a feature is green at every tier but wired to nothing the user touches.
 *
 * Usage:
 *   bun scripts/enforce-coverage.ts            # runs `bun test --coverage` itself
 *   bun test --coverage | bun scripts/enforce-coverage.ts --stdin
 */

import { existsSync } from "node:fs";
import { join, resolve } from "node:path";
import { config } from "./coverage.config.ts";

/** This script lives at packages/polly/scripts/ — one up is the package root. */
const PACKAGE_ROOT = resolve(import.meta.dir, "..");
const TESTS_DIR = join(PACKAGE_ROOT, "tests");

interface CoverageRow {
  /** Package-relative, e.g. `src/shared/lib/state.ts`. */
  file: string;
  funcs: number;
  lines: number;
}

/** `../src/foo.ts` (relative to tests/) → `src/foo.ts` (relative to the package). */
function normalizePath(raw: string): string {
  return raw.replace(/^(?:\.\.\/)+/, "");
}

/**
 * Parse the `bun test --coverage` table. Only `src/**` rows are policy-bearing;
 * test-infra rows (setup.ts, unit/helpers/…) and the `All files` summary are
 * skipped. Column order is `File | % Funcs | % Lines | Uncovered`.
 */
function parseCoverageTable(text: string): CoverageRow[] {
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
    if (!file.startsWith("src/") || Number.isNaN(funcs) || Number.isNaN(lines)) continue;

    rows.push({ file, funcs, lines });
  }
  return rows;
}

interface Violation {
  file: string;
  metric: "lines" | "funcs";
  observed: number;
  required: number;
}

interface Findings {
  violations: Violation[];
  staleExempts: string[];
  missingExemptFiles: string[];
  missingClaimedBy: Array<{ file: string; claimedBy: string }>;
}

/** Check each covered row against the floor (or note an exemption gone stale). */
function evaluateRows(rows: CoverageRow[]): { violations: Violation[]; staleExempts: string[] } {
  const t = config.defaultThreshold;
  const violations: Violation[] = [];
  const staleExempts: string[] = [];

  for (const row of rows) {
    if (config.exempt[row.file]) {
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

/**
 * Every exemption must point at a real source file AND a real claiming test
 * (or carry an explicit `n/a — …` waiver), so the list can't rot into lies.
 */
function validateExemptions(): {
  missingExemptFiles: string[];
  missingClaimedBy: Array<{ file: string; claimedBy: string }>;
} {
  const missingExemptFiles: string[] = [];
  const missingClaimedBy: Array<{ file: string; claimedBy: string }> = [];
  for (const [file, entry] of Object.entries(config.exempt)) {
    if (!existsSync(join(PACKAGE_ROOT, file))) missingExemptFiles.push(file);
    const claimedBy = entry.claimedBy.trim();
    if (!claimedBy.startsWith("n/a") && !existsSync(join(PACKAGE_ROOT, claimedBy))) {
      missingClaimedBy.push({ file, claimedBy });
    }
  }
  return { missingExemptFiles, missingClaimedBy };
}

function evaluate(rows: CoverageRow[]): Findings {
  return { ...evaluateRows(rows), ...validateExemptions() };
}

async function readStdin(): Promise<string> {
  const chunks: string[] = [];
  for await (const chunk of Bun.stdin.stream()) chunks.push(new TextDecoder().decode(chunk));
  return chunks.join("");
}

/** Run `bun test --coverage` in tests/ and return its combined output. */
async function runCoverage(): Promise<string> {
  process.stderr.write("enforce-coverage: running `bun test --coverage` …\n");
  const proc = Bun.spawn(["bun", "test", "--coverage"], {
    cwd: TESTS_DIR,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, err] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  if (proc.exitCode !== 0) {
    process.stderr.write(`enforce-coverage: test run exited ${proc.exitCode}; failing.\n${err}`);
    process.exit(1);
  }
  // The coverage table lands on one of the two streams depending on bun
  // version; concatenating is robust and the parser ignores everything else.
  return `${out}\n${err}`;
}

function report(findings: Findings): boolean {
  const { violations, staleExempts, missingExemptFiles, missingClaimedBy } = findings;
  let ok = true;

  if (missingExemptFiles.length > 0) {
    ok = false;
    process.stderr.write("❌ exempt entries point at source files that no longer exist:\n");
    for (const f of missingExemptFiles) process.stderr.write(`   ${f}\n`);
    process.stderr.write("   The file was renamed/deleted, or the key is a typo.\n");
  }

  if (missingClaimedBy.length > 0) {
    ok = false;
    process.stderr.write("❌ exempt entries claim a test that does not exist:\n");
    for (const { file, claimedBy } of missingClaimedBy) {
      process.stderr.write(`   ${file}  →  claimedBy: ${claimedBy}\n`);
    }
    process.stderr.write(
      '   Fix the path, or use an "n/a — …" waiver if there is genuinely no test.\n'
    );
  }

  if (staleExempts.length > 0) {
    ok = false;
    process.stderr.write(
      "❌ exempt files now meet the floor — promote them (remove from coverage.config.ts):\n"
    );
    for (const f of staleExempts) {
      process.stderr.write(`   ${f}  (reason was: ${config.exempt[f]?.reason ?? "?"})\n`);
    }
  }

  if (violations.length > 0) {
    ok = false;
    process.stderr.write(`❌ ${violations.length} non-exempt file(s) below the floor:\n`);
    for (const v of violations) {
      process.stderr.write(
        `   ${v.file}  ${v.metric}=${v.observed.toFixed(2)}%  (need ≥ ${v.required}%)\n`
      );
    }
    process.stderr.write(
      "   Add unit tests, or exempt with a reason + the higher-tier test that covers it.\n"
    );
  }

  return ok;
}

const useStdin = process.argv.includes("--stdin");
const text = useStdin ? await readStdin() : await runCoverage();
const rows = parseCoverageTable(text);

if (rows.length === 0) {
  process.stderr.write(
    "❌ enforce-coverage: no src/ coverage rows parsed.\n" +
      (useStdin
        ? "   Was `bun test --coverage` piped in?\n"
        : "   Did the test run produce a coverage table?\n")
  );
  process.exit(1);
}

const findings = evaluate(rows);
const ok = report(findings);

if (ok) {
  const exemptCount = Object.keys(config.exempt).length;
  process.stdout.write(
    `✅ coverage policy ok — ${rows.length} src files at floor ${config.defaultThreshold.lines}/${config.defaultThreshold.funcs}, ${exemptCount} exempt (all claims verified)\n`
  );
}
process.exit(ok ? 0 : 1);
