/**
 * Suite orchestration for the browser test runner.
 *
 * Extracted from run.ts so the resilience guarantee — a transient CDP
 * timeout on one file never aborts the whole suite — is a pure function
 * that can be unit-tested without launching a browser. run.ts supplies
 * the real per-file `runFile`; the test suite supplies a fake one.
 */

/** Pass/fail tally for one test file or for a whole suite. */
export interface FileTally {
  passed: number;
  failed: number;
}

/** A transient CDP timeout (renderer stall) — retryable, unlike a red test. */
export function isProtocolError(err: unknown): boolean {
  return err instanceof Error && err.name === "ProtocolError";
}

export function errMessage(err: unknown): string {
  return err instanceof Error ? err.message : String(err);
}

/**
 * Run every test file, isolating each file's failure.
 *
 * - A thrown `ProtocolError` (renderer stall) is retried once on a fresh
 *   page; if the retry also throws, the file is recorded as failed.
 * - Any other thrown error fails only that file.
 * - A file that returns a tally with `failed > 0` (a genuine red test) is
 *   reported as-is and never retried.
 *
 * The loop never rejects: a stall in one file can never abort the suite,
 * so remaining files always execute and report.
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
      if (isProtocolError(err)) {
        log(`  ⚠️  protocol error (${errMessage(err)}) — retrying once on a fresh page`);
        try {
          result = await runFile(testFile);
        } catch (retryErr) {
          log(`  ❌ retry failed: ${errMessage(retryErr)}`);
          result = { passed: 0, failed: 1 };
        }
      } else {
        // A non-protocol error: record the file as failed and keep going,
        // never abort the whole suite.
        log(`  ❌ ${errMessage(err)}`);
        result = { passed: 0, failed: 1 };
      }
    }

    totalPassed += result.passed;
    totalFailed += result.failed;
  }

  return { passed: totalPassed, failed: totalFailed };
}
