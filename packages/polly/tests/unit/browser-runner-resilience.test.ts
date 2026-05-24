/**
 * Regression test for polly#120 — the browser test runner aborting the
 * whole suite on a single file's failure.
 *
 * Before the fix, a thrown error from any one file rejected the runner
 * outright, so every file was reported as failed. `runSuite` must
 * instead contain the error to the offending file and let the remaining
 * files run.
 *
 * polly#138 removed the protocol-error retry branch — the push-based
 * page→runner reporting in run.ts means a CDP stall on the polling
 * path can no longer happen. Per-file error containment, however, is
 * still a load-bearing property and is what these tests cover.
 */

import { describe, expect, test } from "bun:test";
import { errMessage, type FileTally, runSuite } from "../../tools/test/src/browser/runner-core";

const pass: FileTally = { passed: 1, failed: 0 };

describe("errMessage", () => {
  test("extracts an Error's message", () => {
    expect(errMessage(new Error("boom"))).toBe("boom");
  });

  test("stringifies a non-error value", () => {
    expect(errMessage(42)).toBe("42");
  });
});

describe("runSuite — per-file isolation (polly#120)", () => {
  test("a thrown error in one file does not abort the run", async () => {
    const files = ["a.browser.ts", "b.browser.ts", "c.browser.ts"];
    const calls: string[] = [];

    const runFile = async (file: string): Promise<FileTally> => {
      calls.push(file);
      if (file === "b.browser.ts") throw new Error("page error");
      return pass;
    };

    const total = await runSuite(files, runFile, { log: () => {} });

    // Every file ran exactly once and reported — the suite was not aborted.
    expect(calls).toEqual(["a.browser.ts", "b.browser.ts", "c.browser.ts"]);
    // b counts as one failure; a and c still ran and passed.
    expect(total).toEqual({ passed: 2, failed: 1 });
  });

  test("a thrown error is not retried", async () => {
    const files = ["a.browser.ts"];
    const attempts: Record<string, number> = {};

    const runFile = async (file: string): Promise<FileTally> => {
      attempts[file] = (attempts[file] ?? 0) + 1;
      throw new Error("transport error");
    };

    await runSuite(files, runFile, { log: () => {} });

    expect(attempts["a.browser.ts"]).toBe(1);
  });

  test("a genuine red test is reported as-is and never retried", async () => {
    const files = ["a.browser.ts", "b.browser.ts"];
    const attempts: Record<string, number> = {};

    const runFile = async (file: string): Promise<FileTally> => {
      attempts[file] = (attempts[file] ?? 0) + 1;
      // b returns a failing tally without throwing — a normal assertion failure.
      return file === "b.browser.ts" ? { passed: 2, failed: 3 } : pass;
    };

    const total = await runSuite(files, runFile, { log: () => {} });

    expect(attempts["b.browser.ts"]).toBe(1);
    expect(total).toEqual({ passed: 3, failed: 3 });
  });

  test("runSuite never rejects, even when every file throws", async () => {
    const files = ["a.browser.ts", "b.browser.ts"];
    const runFile = async (): Promise<FileTally> => {
      throw new Error("page error");
    };

    const total = await runSuite(files, runFile, { log: () => {} });
    expect(total).toEqual({ passed: 0, failed: 2 });
  });
});
