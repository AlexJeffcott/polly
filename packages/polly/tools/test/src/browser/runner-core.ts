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

export function errMessage(err: unknown): string {
  return err instanceof Error ? err.message : String(err);
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
