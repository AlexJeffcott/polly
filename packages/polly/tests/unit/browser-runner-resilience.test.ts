/**
 * Regression test for polly#120 — the browser test runner aborting the
 * whole suite on a transient CDP timeout.
 *
 * Before the fix, a thrown `ProtocolError` from any one file rejected the
 * runner outright, so every file was reported as failed. `runSuite` must
 * instead contain that error to the offending file: retry it once on a
 * fresh page, and never abort the remaining files.
 */

import { describe, expect, test } from "bun:test";
import {
  errMessage,
  type FileTally,
  isProtocolError,
  runSuite,
} from "../../tools/test/src/browser/runner-core";

/** The exact error Puppeteer throws when a CDP call exceeds protocolTimeout. */
function protocolError(): Error {
  const err = new Error(
    "Runtime.callFunctionOn timed out. Increase the 'protocolTimeout' setting."
  );
  err.name = "ProtocolError";
  return err;
}

const pass: FileTally = { passed: 1, failed: 0 };

describe("isProtocolError", () => {
  test("recognises a Puppeteer ProtocolError", () => {
    expect(isProtocolError(protocolError())).toBe(true);
  });

  test("rejects an ordinary error", () => {
    expect(isProtocolError(new Error("assertion failed"))).toBe(false);
  });

  test("rejects a non-error value", () => {
    expect(isProtocolError("ProtocolError")).toBe(false);
  });
});

describe("errMessage", () => {
  test("extracts an Error's message", () => {
    expect(errMessage(new Error("boom"))).toBe("boom");
  });

  test("stringifies a non-error value", () => {
    expect(errMessage(42)).toBe("42");
  });
});

describe("runSuite — polly#120 resilience", () => {
  test("a transient ProtocolError on one file does not abort the run", async () => {
    const files = ["a.browser.ts", "b.browser.ts", "c.browser.ts"];
    const calls: string[] = [];

    // b stalls once, then succeeds on the retry.
    let bAttempts = 0;
    const runFile = async (file: string): Promise<FileTally> => {
      calls.push(file);
      if (file === "b.browser.ts") {
        bAttempts += 1;
        if (bAttempts === 1) throw protocolError();
      }
      return pass;
    };

    const total = await runSuite(files, runFile, { log: () => {} });

    // Every file ran and reported — the suite was not aborted.
    expect(calls).toEqual([
      "a.browser.ts",
      "b.browser.ts", // first attempt — stalls
      "b.browser.ts", // retry — succeeds
      "c.browser.ts",
    ]);
    // a + b(retry) + c all passed.
    expect(total).toEqual({ passed: 3, failed: 0 });
  });

  test("retry also failing records the file as failed and continues", async () => {
    const files = ["a.browser.ts", "b.browser.ts", "c.browser.ts"];

    const runFile = async (file: string): Promise<FileTally> => {
      if (file === "b.browser.ts") throw protocolError();
      return pass;
    };

    const total = await runSuite(files, runFile, { log: () => {} });

    // b counts as one failure; a and c still ran and passed.
    expect(total).toEqual({ passed: 2, failed: 1 });
  });

  test("a non-protocol error fails only that file and is not retried", async () => {
    const files = ["a.browser.ts", "b.browser.ts", "c.browser.ts"];
    const attempts: Record<string, number> = {};

    const runFile = async (file: string): Promise<FileTally> => {
      attempts[file] = (attempts[file] ?? 0) + 1;
      if (file === "b.browser.ts") throw new Error("unexpected non-protocol failure");
      return pass;
    };

    const total = await runSuite(files, runFile, { log: () => {} });

    // b was tried exactly once — no retry for a non-protocol error.
    expect(attempts["b.browser.ts"]).toBe(1);
    expect(total).toEqual({ passed: 2, failed: 1 });
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

  test("runSuite never rejects, even when every file stalls", async () => {
    const files = ["a.browser.ts", "b.browser.ts"];
    const runFile = async (): Promise<FileTally> => {
      throw protocolError();
    };

    // The promise resolves — it does not reject — so the suite completes.
    const total = await runSuite(files, runFile, { log: () => {} });
    expect(total).toEqual({ passed: 0, failed: 2 });
  });
});
