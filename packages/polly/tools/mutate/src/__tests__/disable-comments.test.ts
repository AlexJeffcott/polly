/**
 * Disable comments: Stryker's `// Stryker disable` syntax and the
 * `polly-mutate` spelling. The generator marks covered mutants Ignored with
 * the comment's reason; the engine warns about comments that cover no mutant
 * or only CompileError ones (the type filter runs on a real tsgo process).
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { generateMutants } from "../engine/generate.ts";
import { runEngine } from "../engine/index.ts";
import type { EngineResult } from "../engine/types.ts";
import { createFixtureProject } from "./fixture-project.ts";

/** "line MutatorName → ignoredReason" for every ignored mutant in `src`. */
function ignored(src: string, lines?: { from: number; to: number }): string[] {
  return generateMutants("t.ts", src, lines ? { lines } : {})
    .mutants.filter((m) => m.ignoredReason)
    .map((m) => `${m.location.start.line} ${m.mutatorName} → ${m.ignoredReason}`);
}

describe("generate", () => {
  test("next-line covers the named mutator on the next line only", () => {
    const src = [
      "// Stryker disable next-line ObjectLiteral: a data table",
      "export const TABLE = { a: [1] };",
      "export const OTHER = { b: 2 };",
    ].join("\n");
    expect(ignored(src)).toEqual(["2 ObjectLiteral → a data table"]);
    const kept = generateMutants("t.ts", src).mutants.filter((m) => !m.ignoredReason);
    expect(kept.map((m) => `${m.location.start.line} ${m.mutatorName}`)).toEqual([
      "2 ArrayDeclaration",
      "3 ObjectLiteral",
    ]);
  });

  test("names ignore case, all covers every mutator, and a list takes commas", () => {
    expect(
      ignored(["// Stryker disable next-line all", "f(a < b);"].join("\n")).map((s) =>
        s.slice(0, s.indexOf(" →"))
      )
    ).toEqual([
      "2 ConditionalExpression",
      "2 ConditionalExpression",
      "2 EqualityOperator",
      "2 EqualityOperator",
    ]);
    expect(
      ignored(
        ["// Stryker disable next-line equalityoperator, ConditionalExpression", "f(a < b);"].join(
          "\n"
        )
      )
    ).toHaveLength(4);
  });

  test("without next-line a comment covers later lines until a restore", () => {
    const src = [
      "f(a && b);",
      "// Stryker disable LogicalOperator: generated",
      "f(c && d);",
      "f(e && g);",
      "// Stryker restore LogicalOperator",
      "f(h && i);",
    ].join("\n");
    expect(ignored(src)).toEqual([
      "3 LogicalOperator → generated",
      "4 LogicalOperator → generated",
    ]);
  });

  test("a restore next-line opens a one-line hole in a disable all", () => {
    const src = [
      "/* Stryker disable all */",
      "f(a && b);",
      "// Stryker restore next-line LogicalOperator",
      "f(c && d);",
    ].join("\n");
    const reason = "Disabled by the comment on line 1";
    expect(ignored(src)).toEqual([
      `2 ConditionalExpression → ${reason}`,
      `2 ConditionalExpression → ${reason}`,
      `2 LogicalOperator → ${reason}`,
      `4 ConditionalExpression → ${reason}`,
      `4 ConditionalExpression → ${reason}`,
    ]);
  });

  test("the polly-mutate spelling is the same directive", () => {
    expect(
      ignored(["// polly-mutate disable next-line LogicalOperator: why", "f(a && b);"].join("\n"))
    ).toEqual(["2 LogicalOperator → why"]);
  });

  test("a verify callsite keeps its own reason", () => {
    const src = ["// Stryker disable next-line all: comment", 'requires(a && b, "m");'].join("\n");
    const [m] = generateMutants("t.ts", src).mutants;
    expect(m?.ignoredReason).toContain("polly#143");
    expect(m?.disabledBy).toBeUndefined();
  });

  test("comments outside a line range are not returned", () => {
    const src = [
      "// Stryker disable next-line all",
      "f(a && b);",
      "// Stryker disable next-line all",
      "f(c && d);",
    ].join("\n");
    const { disableComments } = generateMutants("t.ts", src, { lines: { from: 4, to: 4 } });
    expect(disableComments.map((c) => c.line)).toEqual([3]);
    expect(ignored(src, { from: 4, to: 4 })).toHaveLength(3);
  });

  test("an unknown name is recorded and matches nothing", () => {
    const { disableComments, mutants } = generateMutants(
      "t.ts",
      ["// Stryker disable next-line LogicOperator", "f(a && b);"].join("\n")
    );
    expect(disableComments[0]?.unknown).toEqual(["LogicOperator"]);
    expect(mutants.every((m) => !m.ignoredReason)).toBe(true);
  });
});

const project = createFixtureProject("polly-mutate-disable-", {
  "tsconfig.json": JSON.stringify({
    compilerOptions: {
      strict: true,
      noEmit: true,
      module: "preserve",
      moduleResolution: "bundler",
      target: "esnext",
      allowImportingTsExtensions: true,
    },
    include: ["src/**/*"],
  }),
  "src/kind.ts": [
    'export type Kind = "a" | "b";',
    "// Stryker disable next-line ObjectLiteral: a data table",
    "export const TABLE = { a: 1 };",
    "export function pick(x: number): Kind {",
    "  // Stryker disable next-line StringLiteral: equivalent",
    '  return x > 0 ? "a" : "b";',
    "}",
    "// Stryker disable next-line all: nothing to mutate",
    "export const ONE = 1;",
    "// polly-mutate disable next-line Bogus",
    "export const TWO = 2;",
  ].join("\n"),
  "tests/kind.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { pick } from "../src/kind.ts";',
    'test("pick", () => expect(pick(1)).toBe("a"));',
    'test("pick", () => expect(pick(0)).toBe("b"));',
  ].join("\n"),
});

let result: EngineResult;
beforeAll(async () => {
  result = await runEngine({
    cwd: project.dir,
    targets: [{ file: project.path("src/kind.ts") }],
    testInclude: ["tests/**/*.test.ts"],
    testPreload: [],
    concurrency: 2,
    timeout: { factor: 2, extraMs: 3000 },
    runner: { kind: "bun-test" },
    excludeMutators: [],
    ignoreVerifyCallsites: true,
    contracts: "off",
    mode: "fast",
    coverage: "dynamic",
    cacheDir: null,
    scratchCwd: true,
    typecheck: true,
    reportPath: project.path("reports/mutation.json"),
  });
}, 120_000);
afterAll(() => project.remove());

describe("engine", () => {
  test("a covered mutant is Ignored with the comment's reason", () => {
    const table = result.targets[0]?.results.find((r) => r.mutant.mutatorName === "ObjectLiteral");
    expect(table?.status).toBe("Ignored");
    expect(table?.statusReason).toBe("a data table");
  });

  test("a covered mutant the type filter rejects is CompileError", () => {
    const strings = result.targets[0]?.results.filter(
      (r) => r.mutant.mutatorName === "StringLiteral"
    );
    expect(strings?.map((r) => r.status)).toEqual(["CompileError", "CompileError"]);
  });

  test("comments that do nothing are warnings", () => {
    expect(result.unusedDisableComments).toEqual([
      { file: "src/kind.ts", line: 5, problem: "covers only CompileError mutants" },
      { file: "src/kind.ts", line: 8, problem: "covers no mutant" },
      { file: "src/kind.ts", line: 10, problem: "names no mutator: Bogus" },
      { file: "src/kind.ts", line: 10, problem: "covers no mutant" },
    ]);
  });
});
