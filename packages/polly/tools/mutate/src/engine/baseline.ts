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
 *
 * With contracts on, a red baseline is read for contract violations: a test
 * that drives a handler outside its `requires`, or a handler that breaks its
 * own `ensures`. That is a finding, not flakiness, so it is reported at once
 * and never retried in-tree. The command runner has no per-test results, so
 * a red command is rerun once with contracts off: green there means the
 * command fails only through a contract.
 */
import { relative } from "node:path";
import { type ContractKill, contractKills, parseJunit, testId } from "./junit.ts";
import { type BunTestOutcome, runBunTest } from "./runner.ts";
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
  /** Contracts on: the tests (or the command) that fail through a contract. */
  contractViolations?: ContractKill[];
}

type Attempt = Omit<Baseline, "inTree">;

function failed(reason: string, contractViolations?: ContractKill[]): Attempt {
  return {
    ok: false,
    ms: 0,
    reason,
    tests: [],
    reportedFiles: new Set(),
    ...(contractViolations ? { contractViolations } : {}),
  };
}

const COMMAND = "(command)";

/** A red command rerun with contracts off: green means a contract alone fails it. */
async function commandViolatesContract(
  cfg: EngineConfig,
  cwd: string,
  preloads: string[],
  files: string[]
): Promise<boolean> {
  const off = await runBunTest(
    {
      cwd,
      files,
      preloads,
      contracts: "off",
      bail: false,
      timeoutMs: BASELINE_TIMEOUT_MS,
      captureStderr: true,
    },
    cfg.runner
  );
  return off.exitCode === 0 && !off.timedOut;
}

/** A green run: in matrix mode, its tests from junit (an empty report is a failure). */
function green(cfg: EngineConfig, cwd: string, outcome: BunTestOutcome): Attempt {
  if (cfg.mode === "fast") return { ok: true, ms: outcome.ms, tests: [], reportedFiles: new Set() };
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
        contracts: cfg.contracts,
        bail: false,
        timeoutMs: BASELINE_TIMEOUT_MS,
        captureStderr: true,
        // Contracts on: a red run's failure text says whether a contract caused it.
        junit: cfg.mode === "matrix" || (cfg.contracts !== "off" && cfg.runner.kind === "bun-test"),
      },
      cfg.runner
    );
    if (outcome.exitCode === 0 && !outcome.timedOut) return green(cfg, cwd, outcome);
    last = outcome.timedOut
      ? `timed out after ${BASELINE_TIMEOUT_MS} ms`
      : `exit ${outcome.exitCode}`;
    const failLine = outcome.stderrTail?.match(/\(fail\)[^\n]*/)?.[0];
    if (failLine) last += `: ${failLine}`;
    if (cfg.contracts === "off" || outcome.timedOut) continue;
    // Deterministic, so no retry: a contract is false on the unmutated code.
    const contract = await contractFailure(cfg, cwd, preloads, files, outcome.junitXml, last);
    if (contract) return contract;
  }
  return failed(`baseline red ${BASELINE_ATTEMPTS}× on the selected tests (${last})`);
}

/** The red run as a contract finding, or null when no contract explains it. */
async function contractFailure(
  cfg: EngineConfig,
  cwd: string,
  preloads: string[],
  files: string[],
  junitXml: string | undefined,
  last: string
): Promise<Attempt | null> {
  if (cfg.runner.kind === "command") {
    if (!(await commandViolatesContract(cfg, cwd, preloads, files))) return null;
    return failed(
      `the command fails only with contracts on (POLLY_CONTRACTS=${cfg.contracts}): a scenario violates a contract`,
      [{ test: COMMAND, contracts: [] }]
    );
  }
  const cases = parseJunit(junitXml ?? "", cwd);
  const violations = contractKills(cases, cfg.cwd);
  if (violations.length === 0) return null;
  const red = cases.filter((c) => c.status === "failed").length;
  return failed(
    violations.length === red
      ? `${violations.length} test(s) violate contracts`
      : `baseline red (${last}) and ${violations.length} of ${red} failing test(s) violate contracts`,
    violations
  );
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
  // A contract violation does not depend on the cwd: no in-tree retry.
  if (scratch.ok || !workdirs || scratch.contractViolations) {
    return { ...scratch, inTree: !workdirs };
  }
  const inTree = await measureIn(cfg, cfg.cwd, preloads, target.covering);
  if (inTree.ok) {
    log(
      `${relative(cfg.cwd, target.file)}: tests fail outside ${cfg.cwd} (${scratch.reason}); its mutants run in-tree`
    );
  }
  return { ...inTree, inTree: true };
}
