/**
 * Suite orchestration for the browser test runner.
 *
 * Extracted from run.ts so the resilience guarantee — a failure in one
 * file never aborts the whole suite — is a pure function that can be
 * unit-tested without launching a browser. run.ts supplies the real
 * per-file `runFile`; the test suite supplies a fake one.
 */

/** Pass/fail tally for one test file or for a whole suite. */
export interface FileTally {
  passed: number;
  failed: number;
}

/** One test's outcome, as the in-page harness reports it. */
export interface TestResult {
  name: string;
  passed: boolean;
  error?: string;
}

/**
 * What the page pushes to the runner as it works through a file.
 *
 * The final `__pollyReport` call carries the whole tally, but it never
 * arrives when the page stops running. These events arrive as the suite
 * goes, so a timed-out file can still say how far it got (polly#177).
 */
export type ProgressEvent =
  | { kind: "plan"; total: number }
  | { kind: "start"; name: string }
  | { kind: "result"; name: string; passed: boolean; error?: string };

/** Everything the page managed to say before it went quiet. */
export interface SuiteProgress {
  /** Test count the page announced up front; absent if it never got that far. */
  planned?: number;
  /** Names of tests that began, in order. */
  started: string[];
  /** Outcomes of tests that finished. */
  completed: TestResult[];
}

/**
 * What the renderer was doing when the file timed out.
 *
 * - `looping`   — the main thread never yielded, so JavaScript is still
 *                 running: a runaway loop in the code under test.
 * - `idle`      — the page answers, so the thread is free; an awaited
 *                 promise never settled, or `done()` was never called.
 * - `unknown`   — the state could not be probed (the page or the browser
 *                 had already gone).
 */
export type StallState = "looping" | "idle" | "unknown";

export function errMessage(err: unknown): string {
  return err instanceof Error ? err.message : String(err);
}

/** Empty progress, for a file whose page said nothing at all. */
export function emptyProgress(): SuiteProgress {
  return { started: [], completed: [] };
}

/** Fold one page-pushed event into the accumulated progress. */
export function applyProgress(progress: SuiteProgress, event: ProgressEvent): void {
  if (event.kind === "plan") {
    progress.planned = event.total;
    return;
  }
  if (event.kind === "start") {
    progress.started.push(event.name);
    return;
  }
  progress.completed.push({ name: event.name, passed: event.passed, error: event.error });
}

function describeStall(state: StallState, timeoutMs: number): string {
  const prefix = `timed out after ${timeoutMs}ms`;
  if (state === "looping") {
    return `${prefix} — the page never yielded its main thread, so JavaScript is still running. That is a runaway loop in the code under test, not a stalled runner.`;
  }
  if (state === "idle") {
    return `${prefix} — the page still answers, so its main thread is free. The suite never called done(): an awaited promise never settled.`;
  }
  return `${prefix} — the page stopped reporting and its state could not be probed.`;
}

/**
 * Turn a timed-out file into a tally and the lines to print for it.
 *
 * A timed-out file used to count as a single failure, so the tests it held
 * vanished from the run's totals with no indication — a 9-test file that
 * stalled on its 4th test reported `1 failed` and the tier's count silently
 * lost 9 tests (polly#177). Every test the page announced is now accounted
 * for: the ones that finished keep their real outcome, and the ones that
 * never ran are counted as failures so the tier's total still matches the
 * number of tests in the files.
 */
export function summariseTimeout(
  progress: SuiteProgress,
  timeoutMs: number,
  state: StallState
): { tally: FileTally; lines: string[] } {
  const passed = progress.completed.filter((r) => r.passed).length;
  const completedFailed = progress.completed.length - passed;
  const lines: string[] = [`  ❌ ${describeStall(state, timeoutMs)}`];

  for (const r of progress.completed) {
    lines.push(r.passed ? `  ✅ ${r.name}` : `  ❌ ${r.name}: ${r.error}`);
  }

  const inFlight = progress.started[progress.completed.length];
  if (inFlight !== undefined) {
    lines.push(`  ⏳ stalled in: ${inFlight}`);
  }

  if (progress.planned === undefined) {
    // The page never announced a plan, so there is no honest test count to
    // report. Fall back to the single-failure tally.
    lines.push("  ⚠ the page never reported a test count — counting the file as one failure");
    return { tally: { passed, failed: completedFailed + 1 }, lines };
  }

  const neverFinished = Math.max(progress.planned - progress.completed.length, 0);
  lines.push(
    `  ⚠ ${neverFinished} of ${progress.planned} tests never finished (${passed} passed, ${completedFailed} failed before the stall)`
  );
  // A plan that is fully accounted for still has to fail the file: the page
  // owed a report and never sent one.
  const failed = neverFinished === 0 ? completedFailed + 1 : completedFailed + neverFinished;
  return { tally: { passed, failed }, lines };
}

/**
 * Run every test file, isolating each file's failure.
 *
 * - Any thrown error from `runFile` fails only that file and is logged.
 * - A file that returns a tally with `failed > 0` (a genuine red test)
 *   is reported as-is.
 *
 * The loop never rejects: a failure in one file can never abort the
 * suite, so the remaining files always execute and report.
 */
export async function runSuite(
  testFiles: string[],
  runFile: (testFile: string) => Promise<FileTally>,
  options: {
    label?: (testFile: string) => string;
    log?: (msg: string) => void;
  } = {}
): Promise<FileTally> {
  const label = options.label ?? ((f) => f);
  const log = options.log ?? console.log;

  let totalPassed = 0;
  let totalFailed = 0;

  for (const testFile of testFiles) {
    log(`\n[browser-runner] running ${label(testFile)}`);

    let result: FileTally;
    try {
      result = await runFile(testFile);
    } catch (err) {
      log(`  ❌ ${errMessage(err)}`);
      result = { passed: 0, failed: 1 };
    }

    totalPassed += result.passed;
    totalFailed += result.failed;
  }

  return { passed: totalPassed, failed: totalFailed };
}
