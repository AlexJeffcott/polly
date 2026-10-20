/**
 * The Bun-native mutation engine: generate → select → cache → baseline → run → report.
 *
 *   generate  oxc-parser spans, Stryker-named operators (generate.ts)
 *   select    one probed pass over every test file records which tests run
 *             each mutant (coverage.ts); a mutant no test runs is
 *             NoCoverage. Static selection: the test files whose import
 *             closure reaches the target (graph.ts)
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
import { join, relative } from "node:path";
import { type Baseline, measureBaseline } from "./baseline.ts";
import {
  type CacheEntry,
  cachedResult,
  cacheKey,
  mutantSig,
  readCache,
  readCoverageCache,
  writeCache,
  writeCoverageCache,
} from "./cache.ts";
import {
  COVERAGE_VERSION,
  type Coverage,
  collectCoverage,
  type MutantCoverage,
  type Selection,
  selectionFor,
} from "./coverage.ts";
import { generateMutants } from "./generate.ts";
import {
  buildImportGraph,
  closureOf,
  coveringTests,
  findTestFiles,
  type ImportGraph,
} from "./graph.ts";
import { type JunitCase, killers, LOAD_FAILURE_NAME, loadFailureId, parseJunit } from "./junit.ts";
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

export { collectCoverage, selectionFor } from "./coverage.ts";
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
  /** The test files its baseline runs: every file some mutant selects. */
  covering: string[];
  /** Dynamic coverage: each mutant's tests, by mutant id. Null: every mutant runs `covering`. */
  selections: Map<string, Selection> | null;
  /** Dynamic coverage: the tests in `covering`, for the report's test list. */
  coverageTests: TestRef[];
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

interface Generated {
  file: string;
  mutants: Mutant[];
  compileErrors: Mutant[];
  /** Static selection. */
  covering: string[];
}

async function generateAll(cfg: EngineConfig, graph: ImportGraph | null): Promise<Generated[]> {
  const out: Generated[] = [];
  for (const [index, target] of cfg.targets.entries()) {
    const file = realpathSync(target.file);
    const { mutants, compileErrors } = generateMutants(file, await Bun.file(file).text(), {
      ignoreVerifyCallsites: cfg.ignoreVerifyCallsites,
      lines: target.lines,
      idPrefix: `${index}.`,
      exclude: cfg.excludeMutators,
    });
    out.push({ file, mutants, compileErrors, covering: graph ? coveringTests(graph, file) : [] });
  }
  return out;
}

/** The coverage pass, from the cache when no file the graph knows has changed. */
async function dynamicCoverage(
  cfg: EngineConfig,
  graph: ImportGraph,
  generated: readonly Generated[],
  preloads: string[],
  workdirs: Workdirs | null,
  log: (line: string) => void
): Promise<Coverage | null> {
  const targets = generated.map((g) => ({
    file: g.file,
    mutants: g.mutants.filter((m) => !m.ignoredReason),
    covering: g.covering,
  }));
  const key = cfg.cacheDir
    ? await cacheKey({
        mutants: targets.flatMap((t) => t.mutants),
        closure: [...graph.imports.keys()].sort(),
        projectFiles: projectFiles(cfg),
        settings: {
          coverage: COVERAGE_VERSION,
          targets: targets.map((t) => [t.file, t.mutants.length]),
          tests: graph.testFiles,
        },
      })
    : null;
  const cached = cfg.cacheDir && key ? await readCoverageCache(cfg.cacheDir, key) : null;
  if (cached) {
    log("coverage pass: from cache");
    return cached;
  }
  const started = performance.now();
  const coverage = await collectCoverage({
    cwd: cfg.cwd,
    testFiles: graph.testFiles,
    targets,
    preloads,
    concurrency: cfg.concurrency,
    workdirs,
    log,
  });
  if (!coverage) return null;
  log(
    `coverage pass: ${Object.keys(coverage.tests).length} tests in ` +
      `${((performance.now() - started) / 1000).toFixed(1)} s`
  );
  if (cfg.cacheDir && key) writeCoverageCache(cfg.cacheDir, key, coverage);
  return coverage;
}

function sortedUnique(items: Iterable<string>): string[] {
  return [...new Set(items)].sort();
}

type Picked = Pick<PreparedTarget, "covering" | "selections" | "coverageTests">;

/** Each mutant's tests from the coverage pass; the baseline runs every file any of them picks. */
function dynamicSelection(
  g: Generated,
  target: { mutants: Record<string, MutantCoverage> },
  coverage: Coverage
): Picked {
  const selections = new Map<string, Selection>();
  for (const m of g.mutants) {
    const cov = target.mutants[m.id];
    if (cov) selections.set(m.id, selectionFor(cov, coverage));
  }
  const covering = sortedUnique([...selections.values()].flatMap((sel) => sel.files));
  const coverageTests = covering.flatMap((f) =>
    (coverage.byFile[f] ?? []).flatMap((id) => {
      const t = coverage.tests[id];
      return t ? [{ id: t.id, file: t.file, name: t.name, line: t.line }] : [];
    })
  );
  return { covering, selections, coverageTests };
}

/** The part of the cache key that dynamic selection adds. Ids are positional, so sigs. */
function selectionKey(
  mutants: readonly Mutant[],
  selections: Map<string, Selection> | null
): unknown[] | null {
  if (!selections) return null;
  return mutants.map((m) => {
    const sel = selections.get(m.id);
    return [mutantSig(m), sel?.files ?? [], sel?.namePattern ?? ""];
  });
}

/** The target with its cache key and, on a hit, its cached results. */
async function withCache(
  cfg: EngineConfig,
  graph: ImportGraph | null,
  g: Generated,
  picked: Picked
): Promise<PreparedTarget> {
  const { covering, selections } = picked;
  const settings = {
    mode: cfg.mode,
    timeout: cfg.timeout,
    scratchCwd: cfg.scratchCwd,
    testPreload: cfg.testPreload,
    coverage: cfg.coverage,
    selections: selectionKey(g.mutants, selections),
  };
  // No import graph bounds what a command reads, so its results are never cached.
  const key =
    cfg.cacheDir && graph && covering.length > 0
      ? await cacheKey({
          mutants: g.mutants,
          closure: closureOf(graph, covering),
          projectFiles: projectFiles(cfg),
          settings,
        })
      : null;
  return {
    file: g.file,
    mutants: g.mutants,
    compileErrors: g.compileErrors,
    ...picked,
    covered: cfg.runner.kind === "command" || covering.length > 0,
    cacheKey: key,
    cached: cfg.cacheDir && key ? await readCache(cfg.cacheDir, key) : null,
  };
}

async function prepare(
  cfg: EngineConfig,
  preloads: string[],
  workdirs: Workdirs | null,
  log: (line: string) => void
): Promise<{ prepared: PreparedTarget[]; testFiles: number }> {
  // The command runner selects nothing: every mutant runs the whole command.
  const command = cfg.runner.kind === "command";
  const testFiles = command ? [] : await findTestFiles(cfg.cwd, cfg.testInclude);
  if (!command && testFiles.length === 0) {
    throw new Error(`no test files match ${cfg.testInclude.join(", ")} under ${cfg.cwd}`);
  }
  const graph = command ? null : await buildImportGraph(testFiles);
  const generated = await generateAll(cfg, graph);
  const coverage =
    graph && cfg.coverage === "dynamic"
      ? await dynamicCoverage(cfg, graph, generated, preloads, workdirs, log)
      : null;
  const prepared: PreparedTarget[] = [];
  for (const [index, g] of generated.entries()) {
    const target = coverage?.targets[index];
    if (target?.kind === "static") {
      log(`${relative(cfg.cwd, g.file)}: static test selection (${target.reason})`);
    }
    const picked =
      coverage && target?.kind === "dynamic"
        ? dynamicSelection(g, target, coverage)
        : { covering: g.covering, selections: null, coverageTests: [] };
    prepared.push(await withCache(cfg, graph, g, picked));
  }
  return { prepared, testFiles: testFiles.length };
}

/** Some test runs the mutant: always under static selection, else when coverage picked a file. */
function selected(p: PreparedTarget, mutant: Mutant): boolean {
  return !p.selections || (p.selections.get(mutant.id)?.files.length ?? 0) > 0;
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
  const selection = p.selections?.get(job.mutant.id);
  const files = selection?.files ?? p.covering;
  const coveredBy = selection ? { coveredBy: selection.coveredBy } : {};
  let runCwd = cfg.cwd;
  const attempt = (namePattern: string | undefined) =>
    inCwd(job.inTree ? null : workdirs, cfg.cwd, (cwd) => {
      runCwd = cwd;
      return runBunTest(
        {
          cwd,
          files,
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
          // A filtered run always reports, so a pattern that matched nothing shows.
          junit: matrix || namePattern !== undefined,
          timeoutMs: job.timeoutMs,
          ...(namePattern ? { namePattern } : {}),
        },
        cfg.runner
      );
    });
  let outcome = await attempt(selection?.namePattern);
  let cases: JunitCase[] = outcome.junitXml ? parseJunit(outcome.junitXml, runCwd) : [];
  if (
    selection?.namePattern &&
    !outcome.timedOut &&
    outcome.exitCode !== 0 &&
    matchedNothing(cases)
  ) {
    outcome = await attempt(undefined);
    cases = outcome.junitXml ? parseJunit(outcome.junitXml, runCwd) : [];
  }
  const durationMs = Math.round(outcome.ms);
  const result = { mutant: job.mutant, durationMs, ...coveredBy };
  if (outcome.timedOut) return { ...result, status: "Timeout" };
  if (outcome.exitCode === 0) return { ...result, status: "Survived" };
  if (!matrix) return { ...result, status: "Killed" };
  const ran = new Set(files);
  const reported = new Set([...baseline.reportedFiles].filter((f) => ran.has(f)));
  return { ...result, status: "Killed", killedBy: killers(cases, reported, cfg.cwd) };
}

/** `bun test -t` exits 1 when its pattern matches no test; that is no kill. */
function matchedNothing(cases: readonly JunitCase[]): boolean {
  return cases.length > 0 && cases.every((c) => c.status === "skipped");
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
  for (const t of p.coverageTests) {
    if (!known.has(t.id)) {
      known.add(t.id);
      tests.push(t);
    }
  }
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
      const reason = p.selections ? "no test ran this target" : "no test file imports this target";
      return { mutant, status: "NoCoverage", statusReason: reason };
    }
    if (!selected(p, mutant)) {
      return { mutant, status: "NoCoverage", statusReason: "no test ran this code", coveredBy: [] };
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
    tests: baseline?.ok ? testsFor(cfg, p, baseline, results) : p.coverageTests,
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

  const { prepared, testFiles } = await prepare(cfg, preloads, workdirs, log);
  const totalMutants = prepared.reduce((n, p) => n + p.mutants.length, 0);
  const hits = prepared.filter((p) => p.cached).length;
  log(
    `${prepared.length} target(s), ${totalMutants} mutants, ` +
      (cfg.runner.kind === "command"
        ? `command \`${cfg.runner.argv.join(" ")}\``
        : `${testFiles} test files in scope`) +
      `, ${cfg.mode} mode` +
      (cfg.runner.kind === "bun-test" ? `, ${cfg.coverage} coverage` : "") +
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
      if (!mutant.ignoredReason && selected(p, mutant))
        jobs.push({ target, mutant, timeoutMs, inTree: baseline.inTree });
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
