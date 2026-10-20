/**
 * Dynamic coverage: which tests run each mutant's code.
 *
 * One pass, before any mutant runs: every test file under `tests.include`
 * runs once (split over `concurrency` processes) with the
 * targets served probed (probes.ts) by the preload's coverage mode. Hits land
 * in buckets the preload keeps per test file:
 *
 *   inside test k   the k-th test the file ran; the k-th non-skipped junit
 *                   case names it. A file whose counts differ, or whose tests
 *                   overlapped (concurrent tests), falls back to "between"
 *   between tests   beforeAll of a later describe, timers: the whole file
 *   while loading   module top-level code. Bun shares one module registry
 *                   across the files of a process, so this runs once, in
 *                   whichever file loaded the module first. Such a mutant is
 *                   "static": every file that imports the target or hit any
 *                   of its probes runs it, as whole files
 *
 * Per mutant this gives the test ids that ran it (`coveredBy`) and the test
 * files to run: named tests through `bun test -t`, or whole files. No hit
 * means NoCoverage, decided without running anything. Because the pass runs
 * every test file, reach the import graph cannot see (`mock.module`, a
 * computed `import()`) is seen.
 *
 * Each process runs in a scratch cwd, as baselines do; a red one reruns in the
 * project cwd, since a test that fails early stops before it reaches the code
 * it would have covered.
 *
 * A target keeps static selection (graph.ts) when its probes do not parse, or
 * when the graph says a test imports it but the plugin never served it (a
 * project preload loaded it first). A coverage process that writes no data
 * (it crashed or timed out) turns the whole pass off.
 *
 * Limit: a test that fails only through state an earlier test left behind
 * (a lazy cache filled once) is not selected, so its kill is lost. That is
 * the price of per-test selection, as with Stryker's `perTest`.
 */
import { mkdtempSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { isRecord } from "../../../../src/shared/lib/guards";
import { type JunitCase, parseJunit, testId } from "./junit.ts";
import { instrument } from "./probes.ts";
import { pool, runBunTest } from "./runner.ts";
import type { ContractsMode, Mutant, TestRef } from "./types.ts";
import { inCwd, type Workdirs } from "./workdir.ts";

/** Bump when attribution changes; part of the coverage cache key. */
export const COVERAGE_VERSION = 1;
const COVERAGE_TIMEOUT_MS = 600_000;
/** A longer `-t` pattern runs the whole files instead. */
const MAX_PATTERN = 8_000;

export interface MutantCoverage {
  /** Test ids that ran the mutant's code inside the test body or its hooks. */
  tests: string[];
  /** Test files to run whole: hits between tests, unordered files, static mutants. */
  files: string[];
}

export type TargetCoverage =
  | { kind: "dynamic"; mutants: Record<string, MutantCoverage> }
  | { kind: "static"; reason: string };

export interface CoverageTest extends TestRef {
  /** The full name `bun test -t` matches. */
  filterName: string;
}

export interface Coverage {
  targets: TargetCoverage[];
  /** Every test the pass ran (not skipped), by id. */
  tests: Record<string, CoverageTest>;
  /** Test file → ids of its tests. */
  byFile: Record<string, string[]>;
}

export interface CoverageTarget {
  file: string;
  /** Mutants to probe (ignored ones are left out). */
  mutants: readonly Mutant[];
  /** Static selection: test files whose import closure reaches the target. */
  covering: readonly string[];
}

export interface CoverageRun {
  cwd: string;
  testFiles: readonly string[];
  targets: readonly CoverageTarget[];
  /** Project preloads, then the engine preload. */
  preloads: string[];
  concurrency: number;
  /** Scratch cwds (workdir.ts); null runs in `cwd`. */
  workdirs: Workdirs | null;
  /** POLLY_CONTRACTS for the pass, as for every other run. */
  contracts: ContractsMode;
  log: (line: string) => void;
}

interface FileHits {
  load: number[];
  between: number[];
  tests: number[][];
  overlapped: boolean;
}

interface ChunkHits {
  served: number[];
  outside: number[];
  files: FileHits[];
}

const numbers = (v: unknown): number[] =>
  Array.isArray(v) ? v.filter((x): x is number => typeof x === "number") : [];

function parseHits(raw: unknown): ChunkHits | null {
  if (!isRecord(raw) || !Array.isArray(raw["files"])) return null;
  return {
    served: numbers(raw["served"]),
    outside: numbers(raw["outside"]),
    files: raw["files"].filter(isRecord).map((f) => ({
      load: numbers(f["load"]),
      between: numbers(f["between"]),
      tests: Array.isArray(f["tests"]) ? f["tests"].map(numbers) : [],
      overlapped: f["overlapped"] === true,
    })),
  };
}

function real(path: string): string {
  try {
    return realpathSync(path);
  } catch {
    return path;
  }
}

/** Contiguous slices, so neighbouring files still share a process as in a full run. */
export function chunk<T>(items: readonly T[], n: number): T[][] {
  const count = Math.max(1, Math.min(n, items.length));
  const size = Math.ceil(items.length / count);
  const out: T[][] = [];
  for (let i = 0; i < items.length; i += size) out.push(items.slice(i, i + size));
  return out;
}

/** What one probe was hit by, across every chunk. */
interface ProbeHits {
  tests: Set<string>;
  files: Set<string>;
  /** Files loading when module top-level code hit it. */
  loads: Set<string>;
  static: boolean;
}

function newProbeHits(): ProbeHits {
  return { tests: new Set(), files: new Set(), loads: new Set(), static: false };
}

class Attribution {
  readonly probes = new Map<number, ProbeHits>();
  readonly served = new Set<number>();
  readonly tests: Record<string, CoverageTest> = {};
  readonly byFile: Record<string, string[]> = {};

  constructor(private readonly cwd: string) {}

  private at(probe: number): ProbeHits {
    let hits = this.probes.get(probe);
    if (!hits) {
      hits = newProbeHits();
      this.probes.set(probe, hits);
    }
    return hits;
  }

  private record(c: JunitCase): string {
    const id = testId(this.cwd, c.file, c.name, c.line);
    if (!this.tests[id]) {
      this.tests[id] = { id, file: c.file, name: c.name, line: c.line, filterName: c.filterName };
      const file = real(c.file);
      this.byFile[file] = [...(this.byFile[file] ?? []), id];
    }
    return id;
  }

  /** One chunk: its hits (indexed by the plan's test list) and its junit cases. */
  add(testFiles: readonly string[], hits: ChunkHits, cases: readonly JunitCase[]): void {
    for (const t of hits.served) this.served.add(t);
    for (const p of hits.outside) this.at(p).static = true;
    const ran = new Map<string, JunitCase[]>();
    for (const c of cases) {
      if (c.status === "skipped") continue;
      const file = real(c.file);
      ran.set(file, [...(ran.get(file) ?? []), c]);
    }
    hits.files.forEach((f, i) => {
      const file = testFiles[i];
      if (!file) return;
      const fileCases = ran.get(file) ?? [];
      const ids = fileCases.map((c) => this.record(c));
      for (const p of f.load) {
        const h = this.at(p);
        h.static = true;
        h.loads.add(file);
      }
      for (const p of f.between) this.at(p).files.add(file);
      const ordered = !f.overlapped && f.tests.length === ids.length;
      f.tests.forEach((probes, k) => {
        const id = ids[k];
        for (const p of probes) {
          if (ordered && id) this.at(p).tests.add(id);
          else this.at(p).files.add(file);
        }
      });
    });
  }
}

interface Probed {
  target: number;
  ids: string[];
}

async function planTargets(run: CoverageRun): Promise<{
  plan: { file: string; code: string }[];
  probes: Probed[];
  failed: Map<number, string>;
}> {
  const plan: { file: string; code: string }[] = [];
  const probes: Probed[] = [];
  const failed = new Map<number, string>();
  for (const [target, t] of run.targets.entries()) {
    const probed = instrument(t.file, await Bun.file(t.file).text(), t.mutants, probes.length);
    if (!probed) {
      failed.set(target, "its probed source does not parse");
      continue;
    }
    plan.push({ file: t.file, code: probed.code });
    for (const ids of probed.probes) probes.push({ target, ids });
  }
  return { plan, probes, failed };
}

function sorted(set: Iterable<string>): string[] {
  return [...new Set(set)].sort();
}

/** Every file that touched the target: its static mutants run in all of them. */
function usersOf(
  t: CoverageTarget,
  attribution: Attribution,
  mine: readonly { probe: number }[]
): Set<string> {
  const users = new Set(t.covering);
  for (const { probe } of mine) {
    const h = attribution.probes.get(probe);
    if (!h) continue;
    const testFiles = [...h.tests].flatMap((id) => {
      const file = attribution.tests[id]?.file;
      return file ? [real(file)] : [];
    });
    for (const f of [...testFiles, ...h.files, ...h.loads]) users.add(f);
  }
  return users;
}

function targetCoverage(
  run: CoverageRun,
  target: number,
  attribution: Attribution,
  probes: readonly Probed[]
): TargetCoverage {
  const t = run.targets[target];
  if (!t) return { kind: "static", reason: "missing target" };
  const mine = probes.flatMap((p, probe) => (p.target === target ? [{ probe, ids: p.ids }] : []));
  if (!attribution.served.has(target) && t.covering.length > 0) {
    return {
      kind: "static",
      reason: "a test imports it but the coverage pass never loaded it (a project preload may)",
    };
  }
  const users = usersOf(t, attribution, mine);
  const mutants: Record<string, MutantCoverage> = {};
  for (const { probe, ids } of mine) {
    const h = attribution.probes.get(probe) ?? newProbeHits();
    const files = h.static ? [...users, ...h.files] : [...h.files];
    const cov = { tests: sorted(h.tests), files: sorted(files) };
    for (const id of ids) mutants[id] = cov;
  }
  return { kind: "dynamic", mutants };
}

/** Run the pass. Null when a process wrote no data: every target then keeps static selection. */
export async function collectCoverage(run: CoverageRun): Promise<Coverage | null> {
  const { plan, probes, failed } = await planTargets(run);
  const dir = mkdtempSync(join(tmpdir(), "polly-mutate-coverage-"));
  try {
    const planPath = join(dir, "plan.json");
    writeFileSync(planPath, JSON.stringify({ targets: plan, tests: run.testFiles }));
    const attribution = new Attribution(run.cwd);
    const chunks = chunk(run.testFiles, run.concurrency);
    const outcomes = await pool(chunks, run.concurrency, async (files, i) => {
      const out = join(dir, `hits-${i}.json`);
      const attempt = (workdirs: Workdirs | null) =>
        inCwd(workdirs, run.cwd, async (cwd) => {
          rmSync(out, { force: true });
          const outcome = await runBunTest({
            cwd,
            files,
            preloads: run.preloads,
            env: { POLLY_MUTATE_COVERAGE: planPath, POLLY_MUTATE_COVERAGE_OUT: out },
            contracts: run.contracts,
            bail: false,
            junit: true,
            timeoutMs: COVERAGE_TIMEOUT_MS,
            captureStderr: true,
          });
          const file = Bun.file(out);
          const hits = (await file.exists()) ? parseHits(await file.json()) : null;
          return { outcome, hits, cwd };
        });
      const scratch = await attempt(run.workdirs);
      if (scratch.outcome.exitCode === 0 || !run.workdirs) return scratch;
      run.log(
        `coverage pass: process ${i + 1}/${chunks.length} is red in a scratch cwd; rerun in-tree`
      );
      return attempt(null);
    });
    for (const [i, { outcome, hits, cwd }] of outcomes.entries()) {
      if (!hits) {
        run.log(
          `coverage pass: process ${i + 1}/${chunks.length} wrote no data (${outcome.timedOut ? "timed out" : `exit ${outcome.exitCode}`}); every target keeps static selection`
        );
        return null;
      }
      if (outcome.exitCode !== 0) {
        const failLine = outcome.stderrTail?.match(/\(fail\)[^\n]*/)?.[0] ?? "";
        run.log(
          `coverage pass: tests failed in process ${i + 1}/${chunks.length} (exit ${outcome.exitCode}) ${failLine}`.trim()
        );
      }
      attribution.add(run.testFiles, hits, parseJunit(outcome.junitXml ?? "", cwd));
    }
    const targets = run.targets.map((_, i): TargetCoverage => {
      const reason = failed.get(i);
      if (reason) return { kind: "static", reason };
      return targetCoverage(run, i, attribution, probes);
    });
    return { targets, tests: attribution.tests, byFile: attribution.byFile };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

export interface Selection {
  /** Test files to pass to `bun test`; empty means NoCoverage. */
  files: string[];
  /** `bun test -t`, when every selected test is named. */
  namePattern?: string;
  coveredBy: string[];
}

const escapeRegex = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

export function selectionFor(cov: MutantCoverage, coverage: Coverage): Selection {
  const named = cov.tests.flatMap((id) => {
    const t = coverage.tests[id];
    return t ? [t] : [];
  });
  const files = sorted([...cov.files, ...named.map((t) => real(t.file))]);
  const coveredBy = sorted([...cov.tests, ...cov.files.flatMap((f) => coverage.byFile[f] ?? [])]);
  if (cov.files.length > 0 || named.length === 0) return { files, coveredBy };
  const pattern = `^(?:${sorted(named.map((t) => escapeRegex(t.filterName))).join("|")})$`;
  return pattern.length > MAX_PATTERN
    ? { files, coveredBy }
    : { files, namePattern: pattern, coveredBy };
}
