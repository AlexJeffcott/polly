/**
 * The type filter against a real tsgo process: a fixture project with a
 * strict tsconfig, a target whose literal-union return type rejects some
 * mutants, a target that already fails to type-check (its old error must not
 * be charged to its mutants), and a target no tsconfig includes.
 */
import { afterAll, describe, expect, test } from "bun:test";
import { generateMutants } from "../engine/generate.ts";
import { runEngine } from "../engine/index.ts";
import { tsconfigCandidates, typecheckMutants } from "../engine/typecheck.ts";
import type { Mutant } from "../engine/types.ts";
import { createFixtureProject } from "./fixture-project.ts";

const TSCONFIG = JSON.stringify({
  compilerOptions: {
    strict: true,
    noUnusedLocals: true,
    noUnusedParameters: true,
    allowUnreachableCode: false,
    noEmit: true,
    module: "preserve",
    moduleResolution: "bundler",
    target: "esnext",
    allowImportingTsExtensions: true,
  },
  include: ["src/**/*"],
});

const project = createFixtureProject("polly-mutate-typecheck-", {
  "tsconfig.json": TSCONFIG,
  "src/kind.ts": [
    'export type Kind = "a" | "b";',
    "export function pick(x: number): Kind {",
    '  return x > 0 ? "a" : "b";',
    "}",
    "export function label(k: Kind, hint: string): string {",
    '  if (k === "a") {',
    "    return hint;",
    "  }",
    '  return "none";',
    "}",
  ].join("\n"),
  // `n` is already an error (string to number): mutants must not inherit it.
  "src/stale.ts": [
    'export const n: number = "one";',
    "export function twice(x: number): number {",
    "  return x * 2;",
    "}",
  ].join("\n"),
  // Outside tsconfig's include.
  "lib/outside.ts": "export const neg = (x: number) => x < 0;",
  "tests/kind.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { label, pick } from "../src/kind.ts";',
    'test("pick", () => expect(pick(1)).toBe("a"));',
    'test("label", () => expect(label("a", "h")).toBe("h"));',
  ].join("\n"),
});
afterAll(() => project.remove());

async function mutantsOf(rel: string): Promise<Mutant[]> {
  const file = project.path(rel);
  return generateMutants(file, await Bun.file(file).text()).mutants;
}

const byLine = (mutants: Mutant[], line: number, name: Mutant["mutatorName"]) =>
  mutants.filter((m) => m.location.start.line === line && m.mutatorName === name);

describe("tsconfigCandidates", () => {
  test("nearest first, every ancestor that has one", () => {
    const found = tsconfigCandidates(project.path("src/kind.ts"));
    expect(found[0]).toBe(project.path("tsconfig.json"));
  });
});

describe("typecheckMutants", () => {
  test("a literal-union return rejects the string mutants, with the TS reason", async () => {
    const mutants = await mutantsOf("src/kind.ts");
    const out = await typecheckMutants([{ file: project.path("src/kind.ts"), mutants }], {
      cwd: project.dir,
    });
    expect(out).not.toBeNull();
    if (!out) return;
    expect(out.checked).toBe(mutants.length);
    expect(out.skipped).toEqual([]);
    // `"a"` → `""` on line 3: not a Kind.
    const strings = byLine(mutants, 3, "StringLiteral");
    expect(strings.length).toBeGreaterThan(0);
    for (const m of strings) {
      expect(out.invalid.get(m.id)).toMatch(/^TS2322: Type '""' is not assignable to type 'Kind'/);
    }
    // `pick`'s body → `{}`: a Kind-returning function with no return.
    const [body] = byLine(mutants, 2, "BlockStatement");
    expect(body && out.invalid.get(body.id)).toMatch(/^TS2355:/);
    // `x > 0` → `x >= 0` still returns a Kind; the unused-parameter and
    // unreachable-code rules are relaxed, so `{}` on label's if-block passes too.
    const [boundary] = byLine(mutants, 3, "EqualityOperator");
    expect(boundary && out.invalid.has(boundary.id)).toBe(false);
    const [ifBlock] = byLine(mutants, 6, "BlockStatement");
    expect(ifBlock && out.invalid.has(ifBlock.id)).toBe(false);
    const [always] = byLine(mutants, 6, "ConditionalExpression");
    expect(always && out.invalid.has(always.id)).toBe(false);
  });

  test("an error the file already has is not a verdict", async () => {
    const mutants = await mutantsOf("src/stale.ts");
    const out = await typecheckMutants([{ file: project.path("src/stale.ts"), mutants }], {
      cwd: project.dir,
    });
    expect(out?.checked).toBe(mutants.length);
    // `x * 2` → `x / 2` is still a number.
    const [arith] = byLine(mutants, 3, "ArithmeticOperator");
    expect(arith && out?.invalid.has(arith.id)).toBe(false);
  });

  test("a target no tsconfig includes is skipped, not judged", async () => {
    const mutants = await mutantsOf("lib/outside.ts");
    const lines: string[] = [];
    const out = await typecheckMutants([{ file: project.path("lib/outside.ts"), mutants }], {
      cwd: project.dir,
      log: (l) => lines.push(l),
    });
    expect(out?.invalid.size).toBe(0);
    expect(out?.checked).toBe(0);
    expect(out?.skipped).toEqual([
      { file: project.path("lib/outside.ts"), reason: "no tsconfig.json includes it" },
    ]);
    expect(lines.some((l) => l.includes("lib/outside.ts: no tsconfig.json includes it"))).toBe(
      true
    );
  });
});

describe("runEngine with typecheck", () => {
  test("invalid mutants are CompileError and never run; the rest run as usual", async () => {
    const lines: string[] = [];
    const result = await runEngine(
      {
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
        typecheck: true,
        cacheDir: null,
        scratchCwd: true,
        reportPath: project.path("reports/mutation.json"),
      },
      { log: (l) => lines.push(l) }
    );
    const results = result.targets[0]?.results ?? [];
    const compileErrors = results.filter((r) => r.status === "CompileError");
    expect(compileErrors.length).toBeGreaterThan(0);
    for (const r of compileErrors) {
      expect(r.statusReason).toMatch(/^TS\d+: /);
      expect(r.durationMs).toBeUndefined();
    }
    expect(results.some((r) => r.status === "Killed")).toBe(true);
    expect(lines.some((l) => /^type filter: \d+ of \d+ mutants fail to type-check/.test(l))).toBe(
      true
    );
  }, 60_000);
});
