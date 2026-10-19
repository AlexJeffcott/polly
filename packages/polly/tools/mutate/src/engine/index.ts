/**
 * The Bun-native mutation engine: generate → select → cache → baseline → run → report.
 *
 *   generate  oxc-parser spans, Stryker-named operators (generate.ts)
 *   select    test files whose import closure reaches the target (graph.ts)
 *   cache     a target whose inputs are unchanged reuses its last results (cache.ts)
 *   baseline  run exactly that subset unmutated; it must pass, and its time
 *             sets the per-mutant timeout (baseline.ts)
 *   run       one `bun test` per mutant, the mutant injected by a preload
 *             plugin (preload.ts) — no sandbox copy; each process gets a fresh
 *             scratch cwd (workdir.ts). Fast mode bails at the first failure;
 *             matrix mode runs every test and records each killer (junit.ts)
 *   report    mutation-testing-report-schema JSON (report-writer.ts)
 */
import { realpathSync } from "node:fs";
import { join } from "node:path";
import { type Baseline, measureBaseline } from "./baseline.ts";
import {
  type CacheEntry,
  cachedResult,
  cacheKey,
  mutantSig,
  readCache,
  writeCache,
} from "./cache.ts";
import { generateMutants } from "./generate.ts";
import { buildImportGraph, closureOf, coveringTests, findTestFiles } from "./graph.ts";
import { killers, LOAD_FAILURE_NAME, loadFailureId, parseJunit } from "./junit.ts";
import { toMutationReport, writeReport } from "./report-writer.ts";
import { pool, preloadPath, runBunTest } from "./runner.ts";
import { newPaths, snapshotWorktree } from "./stray-writes.ts";
import type {
  EngineConfig,
  EngineResult,
  Mutant,
  MutantResult,
  TargetSummary,
  TestRef,
} from "./types.ts";
import { createWorkdirs, inCwd, type Workdirs } from "./workdir.ts";

export { applyMutant, generateMutants } from "./generate.ts";
export { buildImportGraph, coveringTests, findTestFiles } from "./graph.ts";
export { toMutationReport, writeReport } from "./report-writer.ts";
export { newPaths, snapshotWorktree } from "./stray-writes.ts";
export type * from "./types.ts";
export { VERIFY_PRIMITIVES } from "./verify-callsites.ts";

export interface EngineHooks {
  log?: (line: string) => void;
  progress?: (done: number, total: number) => void;
}

interface PreparedTarget {
  file: string;
  mutants: Mutant[];
  compileErrors: Mutant[];
  covering: string[];
  /** Something runs against it: a covering test file, or the command runner. */
  covered: boolean;
  cacheKey: string | null;
  cached: CacheEntry | null;
}

/** Files outside the import graph that still change every result. */
function projectFiles(cfg: EngineConfig): string[] {
  return [
    ...cfg.testPreload,
    ...["tsconfig.json", "bunfig.toml", "bun.lock"].map((f) => join(cfg.cwd, f)),
  ];
}

export async function runEngine(cfg: EngineConfig, hooks: EngineHooks = {}): Promise<EngineResult> {
  if (cfg.runner.kind === "command" && cfg.mode === "matrix") {
    throw new Error("matrix mode needs per-test results; the command runner has none");
  }
  const workdirs = cfg.scratchCwd ? createWorkdirs(cfg.cwd) : null;
  try {
    return await run(cfg, hooks, workdirs);
  } finally {
    workdirs?.remove();
  }
}

async function prepare(
  cfg: EngineConfig
): Promise<{ prepared: PreparedTarget[]; testFiles: number }> {
  // The command runner selects nothing: every mutant runs the whole command.
  const command = cfg.runner.kind === "command";
  const testFiles = command ? [] : await findTestFiles(cfg.cwd, cfg.testInclude);
  if (!command && testFiles.length === 0) {
    throw new Error(`no test files match ${cfg.testInclude.join(", ")} under ${cfg.cwd}`);
  }
  const graph = command ? null : await buildImportGraph(testFiles);
  const settings = {
    mode: cfg.mode,
    timeout: cfg.timeout,
    scratchCwd: cfg.scratchCwd,
    testPreload: cfg.testPreload,
  };
  const prepared: PreparedTarget[] = [];
  for (const [index, target] of cfg.targets.entries()) {
    const file = realpathSync(target.file);
    const { mutants, compileErrors } = generateMutants(file, await Bun.file(file).text(), {
      ignoreVerifyCallsites: cfg.ignoreVerifyCallsites,
      lines: target.lines,
      idPrefix: `${index}.`,
      exclude: cfg.excludeMutators,
    });
    const covering = graph ? coveringTests(graph, file) : [];
    // No import graph bounds what a command reads, so its results are never cached.
    const key =
      cfg.cacheDir && graph && covering.length > 0
        ? await cacheKey({
            mutants,
            closure: closureOf(graph, covering),
            projectFiles: projectFiles(cfg),
            settings,
          })
        : null;
    const cached = cfg.cacheDir && key ? await readCache(cfg.cacheDir, key) : null;
    prepared.push({
      file,
      mutants,
      compileErrors,
      covering,
      covered: command || covering.length > 0,
      cacheKey: key,
      cached,
    });
  }
  return { prepared, testFiles: testFiles.length };
}

interface Job {
  target: number;
  mutant: Mutant;
  timeoutMs: number;
  inTree: boolean;
}

async function runMutant(
  cfg: EngineConfig,
  workdirs: Workdirs | null,
  preloads: string[],
  p: PreparedTarget,
  baseline: Baseline,
  job: Job
): Promise<MutantResult> {
  const matrix = cfg.mode === "matrix";
  let runCwd = cfg.cwd;
  const outcome = await inCwd(job.inTree ? null : workdirs, cfg.cwd, (cwd) => {
    runCwd = cwd;
    return runBunTest(
      {
        cwd,
        files: p.covering,
        preloads,
        env: {
          POLLY_MUTATE_FILE: job.mutant.file,
          POLLY_MUTATE_SPAN: JSON.stringify({
            start: job.mutant.start,
            end: job.mutant.end,
            replacement: job.mutant.replacement,
          }),
        },
        bail: !matrix,
        junit: matrix,
        timeoutMs: job.timeoutMs,
      },
      cfg.runner
    );
  });
  const durationMs = Math.round(outcome.ms);
  if (outcome.timedOut) return { mutant: job.mutant, status: "Timeout", durationMs };
  if (outcome.exitCode === 0) return { mutant: job.mutant, status: "Survived", durationMs };
  if (!matrix) return { mutant: job.mutant, status: "Killed", durationMs };
  const cases = parseJunit(outcome.junitXml ?? "", runCwd);
  const killedBy = killers(cases, baseline.reportedFiles, cfg.cwd);
  return { mutant: job.mutant, status: "Killed", durationMs, killedBy };
}

/** A target's summary from the cache: results matched by mutant content. */
function fromCache(p: PreparedTarget, entry: CacheEntry): TargetSummary {
  const bySig = new Map(entry.results.map((r) => [r.sig, r]));
  const results: MutantResult[] = [...p.mutants, ...p.compileErrors].map((mutant) => {
    const hit = bySig.get(mutantSig(mutant));
    if (!hit)
      return { mutant, status: "RuntimeError", statusReason: "missing from the cache entry" };
    const { sig: _sig, ...rest } = hit;
    return { mutant, ...rest };
  });
  results.sort((a, b) => a.mutant.start - b.mutant.start);
  return {
    file: p.file,
    coveringTests: p.covering,
    baselineMs: entry.baselineMs,
    inTree: entry.inTree,
    cached: true,
    tests: entry.tests,
    results,
  };
}

/** The baseline's tests, plus a stand-in for each file a mutant named as produced-no-results. */
function testsFor(
  cfg: EngineConfig,
  p: PreparedTarget,
  baseline: Baseline,
  results: MutantResult[]
): TestRef[] {
  const tests = [...baseline.tests];
  const known = new Set(tests.map((t) => t.id));
  const used = new Set(results.flatMap((r) => r.killedBy ?? []));
  for (const file of p.covering) {
    const id = loadFailureId(cfg.cwd, file);
    if (used.has(id) && !known.has(id)) tests.push({ id, file, name: LOAD_FAILURE_NAME, line: 0 });
  }
  return tests;
}

function summarise(
  cfg: EngineConfig,
  p: PreparedTarget,
  baseline: Baseline | null,
  byId: Map<string, MutantResult>,
  workdirs: Workdirs | null
): TargetSummary {
  const results: MutantResult[] = p.mutants.map((mutant) => {
    if (mutant.ignoredReason)
      return { mutant, status: "Ignored", statusReason: mutant.ignoredReason };
    if (!p.covered) {
      return { mutant, status: "NoCoverage", statusReason: "no test file imports this target" };
    }
    if (!baseline?.ok) return { mutant, status: "RuntimeError", statusReason: baseline?.reason };
    return (
      byId.get(mutant.id) ?? { mutant, status: "RuntimeError", statusReason: "mutant was not run" }
    );
  });
  for (const mutant of p.compileErrors) {
    results.push({ mutant, status: "CompileError", statusReason: "mutated source does not parse" });
  }
  results.sort((a, b) => a.mutant.start - b.mutant.start);
  return {
    file: p.file,
    coveringTests: p.covering,
    baselineMs: baseline?.ok ? Math.round(baseline.ms) : null,
    inTree: baseline?.inTree ?? !workdirs,
    cached: false,
    tests: baseline?.ok ? testsFor(cfg, p, baseline, results) : [],
    results,
  };
}

async function run(
  cfg: EngineConfig,
  hooks: EngineHooks,
  workdirs: Workdirs | null
): Promise<EngineResult> {
  const log = hooks.log ?? (() => undefined);
  const started = performance.now();
  const preloads = [...cfg.testPreload, preloadPath()];
  const beforeRun = snapshotWorktree(cfg.cwd);

  const { prepared, testFiles } = await prepare(cfg);
  const totalMutants = prepared.reduce((n, p) => n + p.mutants.length, 0);
  const hits = prepared.filter((p) => p.cached).length;
  log(
    `${prepared.length} target(s), ${totalMutants} mutants, ` +
      (cfg.runner.kind === "command"
        ? `command \`${cfg.runner.argv.join(" ")}\``
        : `${testFiles} test files in scope`) +
      `, ${cfg.mode} mode` +
      (cfg.cacheDir ? `, ${hits} target(s) from cache` : "")
  );

  const fresh = prepared.filter((p) => !p.cached && p.covered);
  const measured = await pool(fresh, cfg.concurrency, (p) =>
    measureBaseline(cfg, workdirs, preloads, p, log)
  );
  const baselines = new Map(fresh.map((p, i) => [p, measured[i] ?? null]));
  const afterBaselines = snapshotWorktree(cfg.cwd);

  const jobs: Job[] = [];
  prepared.forEach((p, target) => {
    const baseline = baselines.get(p);
    if (!baseline?.ok) return;
    const timeoutMs = Math.round(baseline.ms * cfg.timeout.factor + cfg.timeout.extraMs);
    for (const mutant of p.mutants) {
      if (!mutant.ignoredReason) jobs.push({ target, mutant, timeoutMs, inTree: baseline.inTree });
    }
  });
  // Slowest targets first, so a long tail does not start last.
  jobs.sort((a, b) => b.timeoutMs - a.timeoutMs);

  let done = 0;
  const runResults = await pool(jobs, cfg.concurrency, async (job) => {
    const p = prepared[job.target];
    const baseline = p && baselines.get(p);
    if (!p || !baseline) throw new Error(`job for target ${job.target} has no baseline`);
    const result = await runMutant(cfg, workdirs, preloads, p, baseline, job);
    done++;
    hooks.progress?.(done, jobs.length);
    return result;
  });
  const byId = new Map(runResults.map((r) => [r.mutant.id, r]));

  const targets: TargetSummary[] = prepared.map((p) =>
    p.cached ? fromCache(p, p.cached) : summarise(cfg, p, baselines.get(p) ?? null, byId, workdirs)
  );

  const afterMutants = snapshotWorktree(cfg.cwd);
  const strayWrites = beforeRun
    ? {
        root: beforeRun.root,
        baseline: newPaths(beforeRun, afterBaselines),
        mutants: newPaths(afterBaselines, afterMutants),
      }
    : null;
  for (const path of strayWrites?.mutants ?? []) log(`warning: a mutant run wrote ${path}`);

  // After the last snapshot, so cache writes are never reported as stray.
  if (cfg.cacheDir) {
    targets.forEach((t, i) => {
      const p = prepared[i];
      if (!cfg.cacheDir || !p?.cacheKey || t.cached || t.baselineMs === null) return;
      writeCache(cfg.cacheDir, p.cacheKey, {
        baselineMs: t.baselineMs,
        inTree: t.inTree,
        tests: t.tests,
        results: t.results.map(cachedResult),
      });
    });
  }

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
