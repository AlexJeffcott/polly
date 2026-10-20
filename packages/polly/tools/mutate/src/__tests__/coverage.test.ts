/**
 * Dynamic coverage end to end: real `bun test` processes, the preload's
 * coverage mode, then mutant runs filtered to the tests that ran each mutant.
 *
 * `calc.ts` is reached only through `mock.module` with a computed specifier,
 * which no import names: static selection must call every mutant NoCoverage,
 * dynamic coverage must find and kill them. `sign.ts` has two tests, each
 * running one branch: a mutant in one branch runs only that test.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { chunk } from "../engine/coverage.ts";
import { runEngine } from "../engine/index.ts";
import type { EngineConfig, EngineResult, MutantResult } from "../engine/types.ts";
import { loadMutationReport } from "../ingest.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-coverage-", {
  "src/calc.ts": [
    "export const LIMIT = 2 + 1;",
    "export function big(x: number) {",
    "  if (x > LIMIT) {",
    "    return x * 2;",
    "  }",
    "  return 0;",
    "}",
    "export function unused(x: number) {",
    "  return x - 1;",
    "}",
  ].join("\n"),
  "src/dep.ts": "export function big(_x: number) {\n  return -1;\n}",
  "src/consumer.ts": 'import { big } from "./dep.ts";\nexport const run = (x: number) => big(x);',
  "src/sign.ts": [
    "export function sign(x: number) {",
    "  if (x < 0) {",
    '    return "neg";',
    "  }",
    '  return "pos";',
    "}",
  ].join("\n"),
  "tests/reach.test.ts": [
    'import { expect, mock, test } from "bun:test";',
    'const spec = ["../src/cal", "c.ts"].join("");',
    'mock.module("../src/dep.ts", () => require(spec));',
    'const { run } = await import("../src/consumer.ts");',
    'test("big input doubles", () => expect(run(5)).toBe(10));',
    'test("small input is zero", () => expect(run(2)).toBe(0));',
  ].join("\n"),
  "tests/sign.test.ts": [
    'import { describe, expect, test } from "bun:test";',
    'import { sign } from "../src/sign.ts";',
    'describe("sign", () => {',
    '  test("negative", () => expect(sign(-1)).toBe("neg"));',
    '  test("positive", () => expect(sign(1)).toBe("pos"));',
    "});",
  ].join("\n"),
});

const config = (over: Partial<EngineConfig>): EngineConfig => ({
  cwd: project.dir,
  targets: [{ file: project.path("src/calc.ts") }, { file: project.path("src/sign.ts") }],
  testInclude: ["tests/**/*.test.ts"],
  testPreload: [],
  mode: "matrix",
  coverage: "dynamic",
  concurrency: 2,
  timeout: { factor: 2, extraMs: 3000 },
  runner: { kind: "bun-test" },
  excludeMutators: [],
  ignoreVerifyCallsites: true,
  contracts: "off",
  scratchCwd: true,
  typecheck: false,
  cacheDir: null,
  reportPath: project.path("reports/mutation.json"),
  ...over,
});

let dynamic: EngineResult;
let staticRun: EngineResult;

beforeAll(async () => {
  dynamic = await runEngine(config({}));
  staticRun = await runEngine(
    config({ coverage: "static", mode: "fast", reportPath: project.path("reports/static.json") })
  );
}, 120_000);
afterAll(() => project.remove());

/** The one `mutator` result on `line` of target `t`. */
function at(r: EngineResult, t: number, line: number, mutator: string): MutantResult {
  const hits = (r.targets[t]?.results ?? []).filter(
    (x) => x.mutant.mutatorName === mutator && x.mutant.location.start.line === line
  );
  const [hit] = hits;
  if (!hit || hits.length > 1) throw new Error(`${hits.length} ${mutator} mutants on line ${line}`);
  return hit;
}

describe("dynamic coverage", () => {
  test("static selection cannot see reach through mock.module", () => {
    const statuses = new Set(staticRun.targets[0]?.results.map((r) => r.status));
    expect(statuses).toEqual(new Set(["NoCoverage"]));
    expect(staticRun.targets[0]?.results[0]?.statusReason).toBe("no test file imports this target");
  });

  test("the coverage pass finds that reach, and the mutant is killed by the test that ran it", () => {
    const r = at(dynamic, 0, 4, "ArithmeticOperator");
    expect(r.status).toBe("Killed");
    expect(r.coveredBy).toEqual(["tests/reach.test.ts#big input doubles@5"]);
    expect(r.killedBy).toEqual(["tests/reach.test.ts#big input doubles@5"]);
  });

  test("code no test runs is NoCoverage, decided without a run", () => {
    const r = at(dynamic, 0, 9, "ArithmeticOperator");
    expect(r.status).toBe("NoCoverage");
    expect(r.statusReason).toBe("no test ran this code");
    expect(r.durationMs).toBeUndefined();
  });

  test("a mutant in module top-level code runs every test of the files that load it", () => {
    const r = at(dynamic, 0, 1, "ArithmeticOperator");
    expect(r.coveredBy).toEqual([
      "tests/reach.test.ts#big input doubles@5",
      "tests/reach.test.ts#small input is zero@6",
    ]);
    expect(r.status).toBe("Killed");
  });

  test("a mutant in one branch runs only the test that takes that branch", () => {
    const neg = at(dynamic, 1, 3, "StringLiteral");
    expect(neg.coveredBy).toEqual(["tests/sign.test.ts#sign > negative@4"]);
    expect(neg.killedBy).toEqual(["tests/sign.test.ts#sign > negative@4"]);
    const pos = at(dynamic, 1, 5, "StringLiteral");
    expect(pos.coveredBy).toEqual(["tests/sign.test.ts#sign > positive@5"]);
    expect(pos.killedBy).toEqual(["tests/sign.test.ts#sign > positive@5"]);
  });

  test("the report carries coveredBy, and every id resolves to a listed test", async () => {
    const report = await loadMutationReport(project.path("reports/mutation.json"));
    const ids = new Set(
      Object.values(report.testFiles ?? {}).flatMap((f) => f.tests.map((t) => t.id))
    );
    const covered = Object.values(report.files).flatMap((f) =>
      f.mutants.flatMap((m) => m.coveredBy ?? [])
    );
    expect(covered.length).toBeGreaterThan(0);
    expect(covered.filter((id) => !ids.has(id))).toEqual([]);
  });
});

describe("chunk", () => {
  test("contiguous slices, at most n, none empty", () => {
    expect(chunk([1, 2, 3, 4, 5], 2)).toEqual([
      [1, 2, 3],
      [4, 5],
    ]);
    expect(chunk([1], 4)).toEqual([[1]]);
    expect(chunk([], 3)).toEqual([]);
  });
});
