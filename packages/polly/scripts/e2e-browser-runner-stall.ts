#!/usr/bin/env bun
/**
 * E2e: the browser runner's behaviour when a page stops reporting.
 *
 * polly#177 began as "the browser runner's page freezes mid-file". The page
 * was not frozen: a component under test had entered an unbounded render
 * loop, so the renderer sat at 100% CPU with its main thread never yielding.
 * From the runner's side both look identical — no console output, no report —
 * and it said only "the in-page suite never reported". Three days of work
 * went into a browser-level cause that was never there.
 *
 * Per CLAUDE.md a green unit suite is not proof, so this drives the real
 * runner against real Chrome with three deliberately stalled pages:
 *
 *   1. A page whose test spins forever must be reported as a runaway loop
 *      ("never yielded its main thread"), not as a mystery.
 *   2. A page that stays responsive but never calls done() must be reported
 *      as the different thing it is ("still answers").
 *   3. A stalled file must say which test it stalled in and how many of its
 *      tests never finished.
 *   4. The healthy files in the same run must still pass, and the run's
 *      totals must add up to the number of tests in the files — the count
 *      that silently lost 9 tests before.
 *
 * The fixtures are generated into a temp directory so the repo's own browser
 * tier is never asked to run a file that hangs on purpose.
 */

export const capability = "browser-runner.stall" as const;

import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const PROJECT_ROOT = resolve(import.meta.dir, "..");
const RUNNER = join(PROJECT_ROOT, "tools/test/src/browser/run.ts");
const HARNESS = join(PROJECT_ROOT, "tools/test/src/browser/index.ts");

/** Per-file deadline for the fixtures. Two files stall, so keep it short. */
const TIMEOUT_MS = 8_000;

/**
 * Fixture files, and the tests each one holds.
 *
 * Names are chosen so the healthy files sort on both sides of the stalled
 * ones; the runner's glob order is not part of the contract, but a healthy
 * file after a stalled one is the case that used to fail with
 * `Connection closed.`
 */
const FIXTURES: Array<{ file: string; tests: number; source: string }> = [
  {
    file: "a-healthy.browser.ts",
    tests: 2,
    source: `
      describe("healthy first", () => {
        test("adds", () => { expect(1 + 1).toBe(2); });
        test("concatenates", () => { expect("a" + "b").toBe("ab"); });
      });
      done();
    `,
  },
  {
    file: "b-runaway.browser.ts",
    tests: 3,
    source: `
      describe("runaway", () => {
        test("finishes normally", () => { expect(true).toBeTruthy(); });
        test("never yields the main thread", async () => {
          // The shape of the polly#177 defect, reduced: the page loads and
          // reports normally, then enters synchronous work that never ends,
          // so no timer, microtask or CDP evaluation can run again.
          await new Promise((r) => setTimeout(r, 0));
          while (true) { /* deliberately unbounded */ }
        });
        test("never starts", () => { expect(true).toBeTruthy(); });
      });
      done();
    `,
  },
  {
    file: "c-idle.browser.ts",
    tests: 2,
    source: `
      describe("idle", () => {
        test("finishes normally", () => { expect(true).toBeTruthy(); });
        test("awaits a promise that never settles", async () => {
          await new Promise(() => { /* no resolve, no reject */ });
        });
      });
      done();
    `,
  },
  {
    file: "d-healthy.browser.ts",
    tests: 2,
    source: `
      describe("healthy last", () => {
        test("still runs after a peer stalled", () => { expect(1).toBe(1); });
        test("and reports its result", () => { expect([1, 2]).toHaveLength(2); });
      });
      done();
    `,
  },
  {
    // Exactly one test on purpose. This page loops during module evaluation,
    // so it never reaches DOMContentLoaded and never announces a plan; the
    // runner can only count it as one failure, and the run's arithmetic stays
    // honest only while the file holds one test.
    file: "e-load-loop.browser.ts",
    tests: 1,
    source: `
      describe("load loop", () => {
        test("never gets the chance to run", () => { expect(true).toBeTruthy(); });
      });
      // Before done() is even reached: the document never finishes loading.
      while (true) { /* deliberately unbounded */ }
    `,
  },
];

const TOTAL_TESTS = FIXTURES.reduce((n, f) => n + f.tests, 0);

async function writeFixtures(dir: string): Promise<void> {
  for (const fixture of FIXTURES) {
    const source = `import { describe, test, expect, done } from ${JSON.stringify(HARNESS)};\n${fixture.source}\n`;
    await writeFile(join(dir, fixture.file), source, "utf8");
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const dir = await mkdtemp(join(tmpdir(), "polly-runner-stall-"));
  try {
    await writeFixtures(dir);
    ctx.log(`[e2e] ${FIXTURES.length} fixture files (${TOTAL_TESTS} tests) in ${dir}`);

    const proc = Bun.spawn(["bun", RUNNER, dir], {
      cwd: PROJECT_ROOT,
      env: { ...process.env, POLLY_BROWSER_TIMEOUT_MS: String(TIMEOUT_MS) },
      stdout: "pipe",
      stderr: "pipe",
    });
    const [stdout, stderr, exitCode] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
      proc.exited,
    ]);
    const output = `${stdout}\n${stderr}`;
    ctx.log(output.trim());

    // 1. The stalled files must fail the run, not be swallowed.
    assert(exitCode !== 0, `runner exited 0 despite three stalled files:\n${output}`);

    // 2. A spinning page is named as a runaway loop, not as silence.
    assert(
      output.includes("never yielded its main thread"),
      "the runaway page was not reported as a main-thread stall — the runner " +
        `cannot tell a loop from a freeze again:\n${output}`
    );

    // 3. A responsive page that never reports is the other diagnosis.
    assert(
      output.includes("still answers"),
      `the idle page was not distinguished from the looping one:\n${output}`
    );

    // 4. The stalled file names the test it stopped in.
    assert(
      output.includes("stalled in: runaway > never yields the main thread"),
      `the runner did not name the test that stalled:\n${output}`
    );

    // 5. And says how many of that file's tests never ran.
    assert(
      output.includes("2 of 3 tests never finished"),
      `the runaway file did not account for its unrun tests:\n${output}`
    );
    assert(
      output.includes("1 of 2 tests never finished"),
      `the idle file did not account for its unrun tests:\n${output}`
    );

    // 6. Healthy files on both sides of the stalls still ran and passed.
    for (const name of ["healthy first > adds", "healthy last > and reports its result"]) {
      assert(output.includes(`✅ ${name}`), `a healthy file did not run: ${name}\n${output}`);
    }
    assert(
      !output.includes("Connection closed"),
      `a stalled file took the browser connection down with it:\n${output}`
    );

    // 7. The totals account for every test in every file. Before polly#177 a
    //    stalled file counted as a single failure and its tests vanished.
    const tally = output.match(/\[browser-runner\] (\d+) passed, (\d+) failed/);
    assert(tally !== null, `no final tally line in the output:\n${output}`);
    const passed = Number(tally?.[1]);
    const failed = Number(tally?.[2]);
    assert(
      passed + failed === TOTAL_TESTS,
      `tally reports ${passed + failed} tests, but the files hold ${TOTAL_TESTS} ` +
        `(${passed} passed, ${failed} failed)`
    );
    // 4 healthy + the two tests that did finish inside the stalled files.
    assert(passed === 6, `expected 6 passing tests, got ${passed}`);
    assert(
      output.includes("never reported a test count"),
      `the load-time loop was not reported as a page that never announced a plan:\n${output}`
    );
    ctx.log(
      `[e2e] tally accounts for all ${TOTAL_TESTS} tests: ${passed} passed, ${failed} failed`
    );

    return { pass: true, detail: { passed, failed, totalTests: TOTAL_TESTS } };
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
