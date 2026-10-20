/**
 * Matrix mode end to end: real `bun test` processes with junit, and the
 * written report checked by `verifyMatrix` — the same contract
 * `polly mutate verify` applies. Two test files pin `double`, so its mutants
 * must each carry two killers; `boom.ts` has a mutant that makes a covering
 * file throw at import, which must still name a killer. `idle.ts` is reached
 * only by a test file with no tests: a green run with an empty junit report,
 * which the baseline guard must refuse. Only its arrow runs (at import), so
 * the mutants in the never-called body are NoCoverage.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { runEngine } from "../engine/index.ts";
import type { EngineResult } from "../engine/types.ts";
import { loadMutationReport } from "../ingest.ts";
import { verifyMatrix } from "../verify-matrix.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-matrix-", {
  "src/double.ts": "export const double = (n: number) => n * 2;",
  "src/boom.ts": 'export const ready = true;\nif (!ready) throw new Error("not ready");',
  "src/idle.ts": "export const idle = (n: number) => n + 1;",
  "tests/idle.test.ts": 'import "bun:test";\nimport { idle } from "../src/idle.ts";\nvoid idle;',
  "tests/one.test.ts": [
    'import { describe, expect, test } from "bun:test";',
    'import { double } from "../src/double.ts";',
    'describe("double", () => {',
    '  test("of 2", () => expect(double(2)).toBe(4));',
    "});",
  ].join("\n"),
  "tests/two.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { double } from "../src/double.ts";',
    'test("of 3", () => expect(double(3)).toBe(6));',
  ].join("\n"),
  "tests/boom.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { ready } from "../src/boom.ts";',
    'test("ready", () => expect(ready).toBe(true));',
  ].join("\n"),
});
const reportPath = project.path("reports/mutation.json");
let result: EngineResult;

beforeAll(async () => {
  result = await runEngine({
    cwd: project.dir,
    targets: [
      { file: project.path("src/double.ts") },
      { file: project.path("src/boom.ts") },
      { file: project.path("src/idle.ts") },
    ],
    testInclude: ["tests/**/*.test.ts"],
    testPreload: [],
    mode: "matrix",
    coverage: "dynamic",
    concurrency: 4,
    timeout: { factor: 2, extraMs: 3000 },
    runner: { kind: "bun-test" },
    excludeMutators: [],
    ignoreVerifyCallsites: true,
    scratchCwd: true,
    typecheck: false,
    cacheDir: null,
    reportPath,
  });
}, 120_000);
afterAll(() => project.remove());

describe("matrix mode", () => {
  test("a mutant both test files detect lists both as killers", () => {
    const arith = result.targets[0]?.results.find(
      (r) => r.mutant.mutatorName === "ArithmeticOperator"
    );
    expect(arith?.status).toBe("Killed");
    expect(arith?.killedBy).toEqual([
      "tests/one.test.ts#double > of 2@4",
      "tests/two.test.ts#of 3@3",
    ]);
  });

  test("a mutant that makes a test file throw at import names that file", () => {
    const thrown = result.targets[1]?.results.find(
      (r) => r.mutant.mutatorName === "BooleanLiteral" && r.mutant.replacement === "false"
    );
    expect(thrown?.status).toBe("Killed");
    expect(thrown?.killedBy).toEqual(["tests/boom.test.ts#(file produced no results)@0"]);
  });

  test("a green baseline with an empty junit report fails the target (baseline guard)", () => {
    const idle = result.targets[2];
    expect(idle?.baselineMs).toBeNull();
    const status = (name: string) =>
      new Set(idle?.results.filter((r) => r.mutant.mutatorName === name).map((r) => r.status));
    expect(status("ArrowFunction")).toEqual(new Set(["RuntimeError"]));
    expect(status("ArithmeticOperator")).toEqual(new Set(["NoCoverage"]));
    expect(idle?.results[0]?.statusReason).toContain("junit report holds no test case");
  });

  test("the written report passes the kill-matrix contract", async () => {
    const check = await verifyMatrix({ reportPath });
    const failed = check.checks.filter((c) => !c.ok).map((c) => `${c.name}: ${c.detail}`);
    expect(failed).toEqual([]);
    expect(check.ok).toBe(true);
  });

  test("the report's test list holds the baseline's tests and the stand-in a mutant used", async () => {
    const report = await loadMutationReport(reportPath);
    const ids = Object.values(report.testFiles ?? {}).flatMap((f) => f.tests.map((t) => t.id));
    expect(ids.sort()).toEqual([
      "tests/boom.test.ts#(file produced no results)@0",
      "tests/boom.test.ts#ready@3",
      "tests/one.test.ts#double > of 2@4",
      "tests/two.test.ts#of 3@3",
    ]);
  });
});

describe("fast mode on the same project", () => {
  test("records no killers, so the contract reports the matrix incomplete", async () => {
    const fastReport = project.path("reports/fast.json");
    await runEngine({
      cwd: project.dir,
      targets: [{ file: project.path("src/double.ts") }],
      testInclude: ["tests/**/*.test.ts"],
      testPreload: [],
      mode: "fast",
      coverage: "dynamic",
      concurrency: 4,
      timeout: { factor: 2, extraMs: 3000 },
      runner: { kind: "bun-test" },
      excludeMutators: [],
      ignoreVerifyCallsites: true,
      scratchCwd: true,
      typecheck: false,
      cacheDir: null,
      reportPath: fastReport,
    });
    const check = await verifyMatrix({ reportPath: fastReport });
    expect(check.ok).toBe(false);
    expect(check.checks.find((c) => c.name.startsWith("matrix is complete"))?.ok).toBe(false);
  }, 120_000);
});
