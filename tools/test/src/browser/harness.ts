/**
 * Minimal browser-side test harness for Polly's browser-only modules.
 *
 * Adapted from lingua's tests/browser/harness.ts. Provides describe/test/
 * expect that run inside a Puppeteer-launched browser tab and record results
 * on `window.__testResults` for the Node-side runner to collect.
 *
 * Usage inside a .browser.ts test file:
 *
 *   import { describe, test, expect, done } from "./harness";
 *
 *   describe("my feature", () => {
 *     test("does the thing", async () => {
 *       expect(1 + 1).toBe(2);
 *     });
 *   });
 *
 *   done();
 */

interface TestResult {
  name: string;
  passed: boolean;
  error?: string;
}

const results: TestResult[] = [];
const suites: Array<{
  name: string;
  tests: Array<{ name: string; fn: () => Promise<void> | void }>;
}> = [];

export function describe(name: string, fn: () => void): void {
  suites.push({ name, tests: [] });
  fn();
}

export function test(name: string, fn: () => Promise<void> | void): void {
  const suite = suites[suites.length - 1];
  if (suite) {
    suite.tests.push({ name, fn });
  }
}

export function expect<T>(actual: T) {
  return {
    toBe(expected: T) {
      if (actual !== expected) {
        throw new Error(`Expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
      }
    },
    toEqual(expected: T) {
      if (JSON.stringify(actual) !== JSON.stringify(expected)) {
        throw new Error(`Expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
      }
    },
    toBeDefined() {
      if (actual === undefined || actual === null) {
        throw new Error(`Expected value to be defined, got ${String(actual)}`);
      }
    },
    toBeGreaterThan(expected: number) {
      if ((actual as unknown as number) <= expected) {
        throw new Error(`Expected ${actual} > ${expected}`);
      }
    },
    toBeUndefined() {
      if (actual !== undefined) {
        throw new Error(`Expected undefined, got ${JSON.stringify(actual)}`);
      }
    },
  };
}

/**
 * Run all registered tests and write results to window.__testResults.
 * Call this at the end of every .browser.ts test file.
 */
export async function done(): Promise<void> {
  for (const suite of suites) {
    for (const t of suite.tests) {
      const fullName = `${suite.name} > ${t.name}`;
      try {
        await t.fn();
        results.push({ name: fullName, passed: true });
      } catch (err) {
        results.push({
          name: fullName,
          passed: false,
          error: err instanceof Error ? err.message : String(err),
        });
      }
    }
  }

  (window as unknown as Record<string, unknown>)["__testResults"] = results;
  (window as unknown as Record<string, unknown>)["__done"] = true;
}

/**
 * Wait until a predicate returns true, polling every intervalMs. Rejects
 * after timeoutMs.
 */
export async function waitFor(
  predicate: () => boolean | Promise<boolean>,
  timeoutMs = 5000,
  intervalMs = 25
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (await predicate()) return;
    await new Promise((r) => setTimeout(r, intervalMs));
  }
  throw new Error(`waitFor timed out after ${timeoutMs}ms`);
}
