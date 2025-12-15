/**
 * Test Helpers
 *
 * Built-in utilities for testing extensions with the framework.
 * Automatically exposes test results to window for Playwright validation.
 */

import type { BaseMessage, Context, ExtensionMessage } from "../types/messages";
import type { MessageBus } from "./message-bus";

// Extend Window interface for test results
declare global {
  interface Window {
    __TEST_RESULTS__?: Record<string, unknown>;
  }
}

export interface TestCase {
  name: string;
  fn: () => Promise<unknown>;
  result?: unknown;
  error?: string;
  duration?: number;
}

export interface TestSuite {
  context: Context;
  tests: Map<string, TestCase>;
  results: {
    passed: number;
    failed: number;
    total: number;
    timestamp: number;
  };
}

export class TestRunner<TMessage extends BaseMessage = ExtensionMessage> {
  private suite: TestSuite;
  private bus: MessageBus<TMessage>;

  constructor(context: Context, bus: MessageBus<TMessage>) {
    this.bus = bus;
    this.suite = {
      context,
      tests: new Map(),
      results: {
        passed: 0,
        failed: 0,
        total: 0,
        timestamp: Date.now(),
      },
    };
  }

  /**
   * Add a test case.
   *
   * @example
   * ```typescript
   * const tests = createTestSuite('popup', bus)
   *
   * tests.add('storage works', async () => {
   *   const result = await bus.send({ type: 'TEST_STORAGE' })
   *   return result.success
   * })
   * ```
   */
  add(name: string, fn: () => Promise<unknown>): this {
    this.suite.tests.set(name, { name, fn });
    return this;
  }

  /**
   * Add a test that sends a message and validates the response.
   *
   * @example
   * ```typescript
   * tests.addMessageTest('storage', { type: 'TEST_STORAGE' }, (result) => {
   *   return result.success === true
   * })
   * ```
   */
  addMessageTest<T extends TMessage>(
    name: string,
    message: T,
    validator?: (result: unknown) => boolean
  ): this {
    this.add(name, async () => {
      const result = await this.bus.send(message);
      if (validator) {
        return validator(result);
      }
      return result;
    });
    return this;
  }

  /**
   * Run all tests and store results.
   *
   * @example
   * ```typescript
   * await tests.run() // Results stored at window.__TEST_RESULTS__.popup
   * ```
   */
  async run(): Promise<TestSuite> {
    this.suite.results = {
      passed: 0,
      failed: 0,
      total: this.suite.tests.size,
      timestamp: Date.now(),
    };

    for (const [_name, test] of this.suite.tests) {
      const startTime = Date.now();

      try {
        test.result = await test.fn();
        test.duration = Date.now() - startTime;
        this.suite.results.passed++;
      } catch (error) {
        test.error = error instanceof Error ? error.message : String(error);
        test.duration = Date.now() - startTime;
        this.suite.results.failed++;
      }
    }

    // Expose results to window for Playwright validation
    this.exposeResults();

    return this.suite;
  }

  /**
   * Run a single test by name.
   */
  async runTest(name: string): Promise<TestCase> {
    const test = this.suite.tests.get(name);
    if (!test) {
      throw new Error(`Test not found: ${name}`);
    }

    const startTime = Date.now();

    try {
      test.result = await test.fn();
      test.duration = Date.now() - startTime;
    } catch (error) {
      test.error = error instanceof Error ? error.message : String(error);
      test.duration = Date.now() - startTime;
    }

    return test;
  }

  /**
   * Get test results.
   */
  getResults(): TestSuite {
    return this.suite;
  }

  /**
   * Get a summary of test results.
   */
  getSummary(): {
    context: Context;
    passed: number;
    failed: number;
    total: number;
    duration: number;
    allPassed: boolean;
  } {
    let totalDuration = 0;
    for (const test of this.suite.tests.values()) {
      totalDuration += test.duration || 0;
    }

    return {
      context: this.suite.context,
      passed: this.suite.results.passed,
      failed: this.suite.results.failed,
      total: this.suite.results.total,
      duration: totalDuration,
      allPassed: this.suite.results.failed === 0,
    };
  }

  /**
   * Expose results to window for Playwright validation.
   * @private
   */
  private exposeResults(): void {
    if (typeof window === "undefined") return;

    // Create or get the global test results object
    if (!window.__TEST_RESULTS__) {
      window.__TEST_RESULTS__ = {};
    }
    const globalResults = window.__TEST_RESULTS__;

    // Convert Map to plain object for serialization
    const testsObject: Record<string, Omit<TestCase, "fn">> = {};
    for (const [name, test] of this.suite.tests) {
      testsObject[name] = {
        name: test.name,
        result: test.result,
        ...(test.error !== undefined && { error: test.error }),
        ...(test.duration !== undefined && { duration: test.duration }),
      };
    }

    globalResults[this.suite.context] = {
      tests: testsObject,
      results: this.suite.results,
      summary: this.getSummary(),
    };
  }

  /**
   * Print test results to console.
   */
  printResults(): void {
    console.group(`[${this.suite.context}] Test Results`);

    for (const test of this.suite.tests.values()) {
      if (test.error) {
        console.error(`❌ ${test.name}: ${test.error} (${test.duration}ms)`);
      }
    }

    console.groupEnd();
  }
}

/**
 * Create a test suite for a specific context.
 *
 * @example
 * ```typescript
 * import { createTestSuite } from '@/shared/lib/test-helpers'
 *
 * const tests = createTestSuite('popup', bus)
 *
 * tests.add('storage works', async () => {
 *   const result = await bus.send({ type: 'TEST_STORAGE' })
 *   return result.success
 * })
 *
 * tests.add('tabs query works', async () => {
 *   const result = await bus.send({ type: 'TEST_TABS' })
 *   return result.tabCount > 0
 * })
 *
 * await tests.run()
 * tests.printResults()
 * ```
 */
export function createTestSuite<TMessage extends BaseMessage = ExtensionMessage>(
  context: Context,
  bus: MessageBus<TMessage>
): TestRunner<TMessage> {
  return new TestRunner<TMessage>(context, bus);
}

/**
 * Convenience function to run a quick test and log the result.
 *
 * @example
 * ```typescript
 * await quickTest('Storage', async () => {
 *   const result = await bus.send({ type: 'TEST_STORAGE' })
 *   return result.success
 * })
 * ```
 */
export async function quickTest(name: string, fn: () => Promise<unknown>): Promise<void> {
  const startTime = Date.now();

  try {
    await fn();
  } catch (error) {
    const duration = Date.now() - startTime;
    console.error(
      `❌ ${name}: ${error instanceof Error ? error.message : String(error)} (${duration}ms)`
    );
  }
}
