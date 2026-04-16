/**
 * Browser-side test harness for Polly applications.
 *
 * Provides describe/test/expect/done that run inside a Puppeteer-launched
 * browser tab and record results on window.__testResults for the Node-side
 * runner to collect. Matchers cover both value assertions and DOM element
 * assertions so that Preact component tests and WebRTC adapter tests use
 * the same harness.
 *
 * @example
 * ```typescript
 * import { describe, test, expect, done, flush, cleanup } from "@fairfox/polly/test/browser";
 *
 * const app = document.getElementById("app")!;
 *
 * describe("my feature", () => {
 *   test("renders correctly", async () => {
 *     render(<MyComponent />, app);
 *     await flush();
 *     expect(app.querySelector("h1")).toHaveTextContent("Hello");
 *     cleanup(app);
 *   });
 * });
 *
 * done();
 * ```
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

function assertElement(value: unknown): Element {
  if (!(value instanceof Element)) {
    throw new Error(`Expected an Element, got ${typeof value}: ${String(value)}`);
  }
  return value;
}

export function expect<T>(actual: T) {
  return {
    // ─── Value matchers ───────────────────────────────────────────────
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
    toContain(sub: string) {
      if (!String(actual).includes(sub)) {
        throw new Error(`Expected "${String(actual)}" to contain "${sub}"`);
      }
    },
    toBeTruthy() {
      if (!actual) throw new Error(`Expected truthy, got ${String(actual)}`);
    },
    toBeFalsy() {
      if (actual) throw new Error(`Expected falsy, got ${String(actual)}`);
    },
    toBeNull() {
      if (actual !== null) throw new Error(`Expected null, got ${String(actual)}`);
    },
    toBeDefined() {
      if (actual === undefined || actual === null) {
        throw new Error(`Expected value to be defined, got ${String(actual)}`);
      }
    },
    toBeUndefined() {
      if (actual !== undefined) {
        throw new Error(`Expected undefined, got ${JSON.stringify(actual)}`);
      }
    },
    toBeGreaterThan(expected: number) {
      if (typeof actual !== "number" || actual <= expected) {
        throw new Error(`Expected ${String(actual)} to be greater than ${expected}`);
      }
    },
    toHaveLength(expected: number) {
      const obj = actual;
      const len = obj && typeof obj === "object" && "length" in obj ? Number(obj.length) : -1;
      if (len !== expected) throw new Error(`Expected length ${expected}, got ${len}`);
    },
    toExist() {
      if (actual == null) throw new Error(`Expected value to exist, got ${String(actual)}`);
    },

    // ─── DOM element matchers ─────────────────────────────────────────
    toHaveTextContent(expected: string) {
      const el = assertElement(actual);
      if (!el.textContent?.includes(expected)) {
        throw new Error(
          `Expected text content to include ${JSON.stringify(expected)}, got ${JSON.stringify(el.textContent)}`
        );
      }
    },
    toBeChecked() {
      const el = assertElement(actual);
      if (!(el instanceof HTMLInputElement) || !el.checked) {
        throw new Error("Expected element to be checked");
      }
    },
    toBeDisabled() {
      const el = assertElement(actual);
      if (!el.hasAttribute("disabled") && el.getAttribute("aria-disabled") !== "true") {
        throw new Error("Expected element to be disabled");
      }
    },
    toHaveValue(expected: string) {
      const el = assertElement(actual);
      const inputEl =
        el instanceof HTMLInputElement || el instanceof HTMLTextAreaElement ? el : null;
      if (!inputEl || inputEl.value !== expected) {
        throw new Error(
          `Expected value ${JSON.stringify(expected)}, got ${JSON.stringify(inputEl?.value ?? "(not an input)")}`
        );
      }
    },
    toHaveAttribute(name: string, value?: string) {
      const el = assertElement(actual);
      if (!el.hasAttribute(name)) {
        throw new Error(`Expected element to have attribute "${name}"`);
      }
      if (value !== undefined && el.getAttribute(name) !== value) {
        throw new Error(
          `Expected attribute "${name}" to be ${JSON.stringify(value)}, got ${JSON.stringify(el.getAttribute(name))}`
        );
      }
    },

    // ─── .not variants ────────────────────────────────────────────────
    not: {
      toBe(expected: T) {
        if (actual === expected) {
          throw new Error(`Expected value NOT to be ${JSON.stringify(expected)}`);
        }
      },
      toEqual(expected: T) {
        if (JSON.stringify(actual) === JSON.stringify(expected)) {
          throw new Error(`Expected value NOT to equal ${JSON.stringify(expected)}`);
        }
      },
      toContain(sub: string) {
        if (String(actual).includes(sub)) {
          throw new Error(`Expected "${String(actual)}" NOT to contain "${sub}"`);
        }
      },
      toBeNull() {
        if (actual === null) throw new Error("Expected value NOT to be null");
      },
      toExist() {
        if (actual != null) throw new Error(`Expected value NOT to exist, got ${String(actual)}`);
      },
      toBeChecked() {
        const el = assertElement(actual);
        if (el instanceof HTMLInputElement && el.checked) {
          throw new Error("Expected element NOT to be checked");
        }
      },
      toBeDisabled() {
        const el = assertElement(actual);
        if (el.hasAttribute("disabled") || el.getAttribute("aria-disabled") === "true") {
          throw new Error("Expected element NOT to be disabled");
        }
      },
      toHaveAttribute(name: string) {
        const el = assertElement(actual);
        if (el.hasAttribute(name)) {
          throw new Error(`Expected element NOT to have attribute "${name}"`);
        }
      },
    },
  };
}

/**
 * Flush microtasks and pending DOM updates. Call after signal assignments
 * or render calls to give the reactive system and the browser a chance to
 * settle before asserting on the result.
 */
export function flush(ms = 50): Promise<void> {
  return new Promise((r) => setTimeout(r, ms));
}

/**
 * Clear a container's rendered content. Call at the end of each test to
 * prevent state leaking between tests. If you use Preact's render(), pass
 * the same container; the function calls render(null, container) if Preact
 * is available, otherwise sets innerHTML to "".
 */
export function cleanup(container: Element): void {
  container.innerHTML = "";
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
