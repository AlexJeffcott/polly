/**
 * The Bun-native mutation engine: generate → select → baseline → run → report.
 *
 *   generate  oxc-parser spans, Stryker-named operators (generate.ts)
 *   select    test files whose import closure reaches the target (graph.ts)
 *   baseline  run exactly that subset unmutated; it must pass, and its time
 *             sets the per-mutant timeout
 *   run       one `bun test --bail` per mutant, the mutant injected by a
 *             preload plugin (preload.ts) — no sandbox copy
 *   report    mutation-testing-report-schema JSON (report-writer.ts)
 */
import { realpathSync } from "node:fs";
import { generateMutants } from "./generate.ts";
import { buildImportGraph, coveringTests, findTestFiles } from "./graph.ts";
import { toMutationReport, writeReport } from "./report-writer.ts";
import { pool, preloadPath, runBunTest } from "./runner.ts";
import { newPaths, snapshotWorktree } from "./stray-writes.ts";
import type { EngineConfig, EngineResult, Mutant, MutantResult, TargetSummary } from "./types.ts";

export { applyMutant, generateMutants } from "./generate.ts";
export { buildImportGraph, coveringTests, findTestFiles } from "./graph.ts";
export { toMutationReport, writeReport } from "./report-writer.ts";
export { newPaths, snapshotWorktree } from "./stray-writes.ts";
export type * from "./types.ts";
export { VERIFY_PRIMITIVES } from "./verify-callsites.ts";

/** Attempts before a red baseline marks a target untrustworthy (flaky subsets do exist). */
const BASELINE_ATTEMPTS = 3;
const BASELINE_TIMEOUT_MS = 300_000;

export interface EngineHooks {
  log?: (line: string) => void;
  progress?: (done: number, total: number) => void;
}

interface PreparedTarget {
  file: string;
  mutants: Mutant[];
  compileErrors: Mutant[];
  covering: string[];
}

interface Baseline {
  ok: boolean;
  ms: number;
  reason?: string;
}

async function measureBaseline(
  cfg: EngineConfig,
  preloads: string[],
  files: string[]
): Promise<Baseline> {
  let last = "";
  for (let attempt = 1; attempt <= BASELINE_ATTEMPTS; attempt++) {
    const outcome = await runBunTest({
      cwd: cfg.cwd,
      files,
      preloads,
      bail: false,
      timeoutMs: BASELINE_TIMEOUT_MS,
      captureStderr: true,
    });
    if (outcome.exitCode === 0 && !outcome.timedOut) return { ok: true, ms: outcome.ms };
    last = outcome.timedOut
      ? `timed out after ${BASELINE_TIMEOUT_MS} ms`
      : `exit ${outcome.exitCode}`;
    const failLine = outcome.stderrTail?.match(/\(fail\)[^\n]*/)?.[0];
    if (failLine) last += `: ${failLine}`;
  }
  return {
    ok: false,
    ms: 0,
    reason: `baseline red ${BASELINE_ATTEMPTS}× on the selected tests (${last})`,
  };
}

export async function runEngine(cfg: EngineConfig, hooks: EngineHooks = {}): Promise<EngineResult> {
  const log = hooks.log ?? (() => undefined);
  const started = performance.now();
  const preloads = [...cfg.testPreload, preloadPath()];
  const beforeRun = snapshotWorktree(cfg.cwd);

  const testFiles = await findTestFiles(cfg.cwd, cfg.testInclude);
  if (testFiles.length === 0) {
    throw new Error(`no test files match ${cfg.testInclude.join(", ")} under ${cfg.cwd}`);
  }
  const graph = await buildImportGraph(testFiles);

  const prepared: PreparedTarget[] = [];
  for (const [index, target] of cfg.targets.entries()) {
    const file = realpathSync(target.file);
    const { mutants, compileErrors } = generateMutants(file, await Bun.file(file).text(), {
      ignoreVerifyCallsites: cfg.ignoreVerifyCallsites,
      lines: target.lines,
      idPrefix: `${index}.`,
    });
    prepared.push({ file, mutants, compileErrors, covering: coveringTests(graph, file) });
  }
  const totalMutants = prepared.reduce((n, p) => n + p.mutants.length, 0);
  log(
    `${prepared.length} target(s), ${totalMutants} mutants, ${testFiles.length} test files in scope`
  );

  const baselines = await pool(prepared, cfg.concurrency, (p) =>
    p.covering.length === 0 ? Promise.resolve(null) : measureBaseline(cfg, preloads, p.covering)
  );

  const afterBaselines = snapshotWorktree(cfg.cwd);

  interface Job {
    target: number;
    mutant: Mutant;
    timeoutMs: number;
  }
  const jobs: Job[] = [];
  prepared.forEach((p, target) => {
    const baseline = baselines[target];
    if (!baseline?.ok) return;
    const timeoutMs = Math.round(baseline.ms * cfg.timeout.factor + cfg.timeout.extraMs);
    for (const mutant of p.mutants)
      if (!mutant.ignoredReason) jobs.push({ target, mutant, timeoutMs });
  });
  // Slowest targets first, so a long tail does not start last.
  jobs.sort((a, b) => b.timeoutMs - a.timeoutMs);

  let done = 0;
  const runResults = await pool(jobs, cfg.concurrency, async (job): Promise<MutantResult> => {
    const p = prepared[job.target];
    const outcome = await runBunTest({
      cwd: cfg.cwd,
      files: p?.covering ?? [],
      preloads,
      env: {
        POLLY_MUTATE_FILE: job.mutant.file,
        POLLY_MUTATE_SPAN: JSON.stringify({
          start: job.mutant.start,
          end: job.mutant.end,
          replacement: job.mutant.replacement,
        }),
      },
      bail: true,
      timeoutMs: job.timeoutMs,
    });
    done++;
    hooks.progress?.(done, jobs.length);
    const status = outcome.timedOut ? "Timeout" : outcome.exitCode === 0 ? "Survived" : "Killed";
    return { mutant: job.mutant, status, durationMs: Math.round(outcome.ms) };
  });
  const byId = new Map(runResults.map((r) => [r.mutant.id, r]));

  const targets: TargetSummary[] = prepared.map((p, target) => {
    const baseline = baselines[target];
    const results: MutantResult[] = p.mutants.map((mutant) => {
      if (mutant.ignoredReason)
        return { mutant, status: "Ignored", statusReason: mutant.ignoredReason };
      if (p.covering.length === 0) {
        return { mutant, status: "NoCoverage", statusReason: "no test file imports this target" };
      }
      if (!baseline?.ok) return { mutant, status: "RuntimeError", statusReason: baseline?.reason };
      return (
        byId.get(mutant.id) ?? {
          mutant,
          status: "RuntimeError",
          statusReason: "mutant was not run",
        }
      );
    });
    for (const mutant of p.compileErrors) {
      results.push({
        mutant,
        status: "CompileError",
        statusReason: "mutated source does not parse",
      });
    }
    results.sort((a, b) => a.mutant.start - b.mutant.start);
    return {
      file: p.file,
      coveringTests: p.covering,
      baselineMs: baseline?.ok ? Math.round(baseline.ms) : null,
      results,
    };
  });

  const afterMutants = snapshotWorktree(cfg.cwd);
  const strayWrites = beforeRun
    ? {
        root: beforeRun.root,
        baseline: newPaths(beforeRun, afterBaselines),
        mutants: newPaths(afterBaselines, afterMutants),
      }
    : null;
  for (const path of strayWrites?.mutants ?? []) log(`warning: a mutant run wrote ${path}`);

  const result: EngineResult = {
    targets,
    wallMs: Math.round(performance.now() - started),
    strayWrites,
  };
  await writeReport(await toMutationReport(result, cfg.cwd), cfg.reportPath);
  return result;
}

/** Stryker's score: detected / (detected + undetected); ignored and invalid mutants do not count. */
export function mutationScore(results: readonly MutantResult[]): number | null {
  let detected = 0;
  let valid = 0;
  for (const r of results) {
    if (r.status === "Killed" || r.status === "Timeout") detected++;
    if (
      r.status === "Killed" ||
      r.status === "Timeout" ||
      r.status === "Survived" ||
      r.status === "NoCoverage"
    )
      valid++;
  }
  return valid === 0 ? null : (100 * detected) / valid;
}
