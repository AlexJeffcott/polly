/**
 * Regression test for polly#120 — the browser test runner aborting the
 * whole suite on a single file's failure.
 *
 * Before the fix, a thrown error from any one file rejected the runner
 * outright, so every file was reported as failed. `runSuite` must
 * instead contain the error to the offending file and let the remaining
 * files run.
 *
 * polly#177 added the timeout summary: a file whose page stops part-way
 * through must report the tests it never ran, so the tier's total still
 * matches the number of tests in the files instead of silently losing them.
 *
 * polly#138 removed the protocol-error retry branch — the push-based
 * page→runner reporting in run.ts means a CDP stall on the polling
 * path can no longer happen. Per-file error containment, however, is
 * still a load-bearing property and is what these tests cover.
 */

import { describe, expect, test } from "bun:test";
import {
  applyProgress,
  emptyProgress,
  errMessage,
  type FileTally,
  runSuite,
  summariseTimeout,
} from "../../tools/test/src/browser/runner-core";

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

describe("summariseTimeout — accounting for a stalled file (polly#177)", () => {
  /** A page that announced 9 tests and finished the first three. */
  function partway() {
    const progress = emptyProgress();
    applyProgress(progress, { kind: "plan", total: 9 });
    for (const name of ["one", "two", "three"]) {
      applyProgress(progress, { kind: "start", name });
      applyProgress(progress, { kind: "result", name, passed: true });
    }
    applyProgress(progress, { kind: "start", name: "four" });
    return progress;
  }

  test("counts every test the page owed, not the file as one failure", () => {
    const { tally } = summariseTimeout(partway(), 60000, "looping");

    // 3 finished and passed; the 4th plus the 5 never started are failures.
    expect(tally).toEqual({ passed: 3, failed: 6 });
    expect(tally.passed + tally.failed).toBe(9);
  });

  test("names the test that was in flight when the page stopped", () => {
    const { lines } = summariseTimeout(partway(), 60000, "looping");

    expect(lines.some((l) => l.includes("stalled in: four"))).toBe(true);
    expect(lines.some((l) => l.includes("5 of 9 tests never finished"))).toBe(false);
    expect(lines.some((l) => l.includes("6 of 9 tests never finished"))).toBe(true);
  });

  test("a looping page and an idle page are reported differently", () => {
    const looping = summariseTimeout(partway(), 60000, "looping").lines[0] ?? "";
    const idle = summariseTimeout(partway(), 60000, "idle").lines[0] ?? "";

    expect(looping).toContain("never yielded its main thread");
    expect(idle).toContain("still answers");
  });

  test("keeps a failed test's own error rather than folding it into the count", () => {
    const progress = emptyProgress();
    applyProgress(progress, { kind: "plan", total: 2 });
    applyProgress(progress, { kind: "start", name: "red" });
    applyProgress(progress, { kind: "result", name: "red", passed: false, error: "boom" });
    applyProgress(progress, { kind: "start", name: "stuck" });

    const { tally, lines } = summariseTimeout(progress, 1000, "looping");

    expect(tally).toEqual({ passed: 0, failed: 2 });
    expect(lines.some((l) => l.includes("red: boom"))).toBe(true);
  });

  test("falls back to a single failure when the page never announced a plan", () => {
    const { tally, lines } = summariseTimeout(emptyProgress(), 1000, "unknown");

    expect(tally).toEqual({ passed: 0, failed: 1 });
    expect(lines.some((l) => l.includes("never reported a test count"))).toBe(true);
  });

  test("a page that finished every test but never reported still fails the file", () => {
    const progress = emptyProgress();
    applyProgress(progress, { kind: "plan", total: 1 });
    applyProgress(progress, { kind: "start", name: "only" });
    applyProgress(progress, { kind: "result", name: "only", passed: true });

    const { tally } = summariseTimeout(progress, 1000, "idle");

    expect(tally).toEqual({ passed: 1, failed: 1 });
  });
});
