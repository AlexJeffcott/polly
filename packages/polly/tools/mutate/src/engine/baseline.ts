/**
 * The baseline: a target's covering tests, run once with the injection
 * preload and no mutant. It must pass — a mutant "killed" by an already-red
 * test proves nothing — and its time sets the per-mutant timeout.
 *
 * Scratch cwd first. When that is red, try the project cwd: green there means
 * the tests depend on the cwd (fixtures read relative to it, say), so the
 * target runs in-tree, where the stray-write guard still reports leaks.
 *
 * In matrix mode the baseline also records every test it ran. A green run
 * whose junit report holds no test case means the reporter broke; the matrix
 * would then be empty without any error, so the target fails instead.
 */
import { relative } from "node:path";
import { parseJunit, testId } from "./junit.ts";
import { runBunTest } from "./runner.ts";
import type { EngineConfig, TestRef } from "./types.ts";
import { inCwd, type Workdirs } from "./workdir.ts";

/** Attempts before a red baseline marks a target untrustworthy (flaky subsets do exist). */
const BASELINE_ATTEMPTS = 3;
const BASELINE_TIMEOUT_MS = 300_000;

export interface Baseline {
  ok: boolean;
  ms: number;
  reason?: string;
  /** The target's tests need the project cwd, so its mutants run there. */
  inTree: boolean;
  /** Matrix mode: the tests that ran. */
  tests: TestRef[];
  /** Matrix mode: test files that reported at least one case. */
  reportedFiles: Set<string>;
}

type Attempt = Omit<Baseline, "inTree">;

function failed(reason: string): Attempt {
  return { ok: false, ms: 0, reason, tests: [], reportedFiles: new Set() };
}

async function measureIn(
  cfg: EngineConfig,
  cwd: string,
  preloads: string[],
  files: string[]
): Promise<Attempt> {
  let last = "";
  for (let attempt = 1; attempt <= BASELINE_ATTEMPTS; attempt++) {
    const outcome = await runBunTest(
      {
        cwd,
        files,
        preloads,
        bail: false,
        timeoutMs: BASELINE_TIMEOUT_MS,
        captureStderr: true,
        junit: cfg.mode === "matrix",
      },
      cfg.runner
    );
    if (outcome.exitCode === 0 && !outcome.timedOut) {
      if (cfg.mode === "fast")
        return { ok: true, ms: outcome.ms, tests: [], reportedFiles: new Set() };
      const cases = parseJunit(outcome.junitXml ?? "", cwd);
      if (cases.length === 0) {
        return failed("baseline passed but its junit report holds no test case (reporter broke?)");
      }
      return {
        ok: true,
        ms: outcome.ms,
        tests: cases.map((c) => ({
          id: testId(cfg.cwd, c.file, c.name, c.line),
          file: c.file,
          name: c.name,
          line: c.line,
        })),
        reportedFiles: new Set(cases.map((c) => c.file)),
      };
    }
    last = outcome.timedOut
      ? `timed out after ${BASELINE_TIMEOUT_MS} ms`
      : `exit ${outcome.exitCode}`;
    const failLine = outcome.stderrTail?.match(/\(fail\)[^\n]*/)?.[0];
    if (failLine) last += `: ${failLine}`;
  }
  return failed(`baseline red ${BASELINE_ATTEMPTS}× on the selected tests (${last})`);
}

export async function measureBaseline(
  cfg: EngineConfig,
  workdirs: Workdirs | null,
  preloads: string[],
  target: { file: string; covering: string[] },
  log: (line: string) => void
): Promise<Baseline> {
  const scratch = await inCwd(workdirs, cfg.cwd, (cwd) =>
    measureIn(cfg, cwd, preloads, target.covering)
  );
  if (scratch.ok || !workdirs) return { ...scratch, inTree: !workdirs };
  const inTree = await measureIn(cfg, cfg.cwd, preloads, target.covering);
  if (inTree.ok) {
    log(
      `${relative(cfg.cwd, target.file)}: tests fail outside ${cfg.cwd} (${scratch.reason}); its mutants run in-tree`
    );
  }
  return { ...inTree, inTree: true };
}
