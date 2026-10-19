import { describe, expect, test } from "bun:test";
import { applyMutant, generateMutants, lineIndex } from "../engine/generate.ts";
import type { Mutant } from "../engine/types.ts";

/** The edits generated for `src`, as "MutatorName: original → replacement". */
function edits(src: string, file = "t.ts"): string[] {
  return generateMutants(file, src).mutants.map(
    (m) => `${m.mutatorName}: ${src.slice(m.start, m.end)} → ${m.replacement}`
  );
}

describe("operators", () => {
  test("EqualityOperator follows Stryker's boundary and negation pairs", () => {
    expect(edits("f(a < b);")).toEqual(["EqualityOperator: < → <=", "EqualityOperator: < → >="]);
    expect(edits("f(a === b);")).toEqual(["EqualityOperator: === → !=="]);
  });

  test("ArithmeticOperator skips string concatenation", () => {
    expect(edits("f(a + b);")).toEqual(["ArithmeticOperator: + → -"]);
    expect(edits('f("x" + b);')).toEqual(['StringLiteral: "x" → ""']);
  });

  test("LogicalOperator", () => {
    expect(edits("f(a && b);")).toEqual(["LogicalOperator: && → ||"]);
    expect(edits("f(a ?? b);")).toEqual(["LogicalOperator: ?? → &&"]);
  });

  test("BooleanLiteral flips literals and drops logical not", () => {
    expect(edits("f(true);")).toEqual(["BooleanLiteral: true → false"]);
    expect(edits("f(!a);")).toEqual(["BooleanLiteral: ! → "]);
  });

  test("ConditionalExpression: both ways for if/ternary, false only for loops", () => {
    expect(edits("x = a ? 1 : 2;")).toEqual([
      "ConditionalExpression: a → true",
      "ConditionalExpression: a → false",
    ]);
    expect(edits("while (a) g();")).toEqual(["ConditionalExpression: a → false"]);
  });

  test("BlockStatement empties non-empty blocks but not a constructor that calls super", () => {
    expect(edits("function f() { g(); }")).toEqual(["BlockStatement: { g(); } → {}"]);
    const derived = "class B extends A { constructor() { super(); } }";
    expect(edits(derived)).toEqual([]);
  });

  test("StringLiteral replaces values, not names", () => {
    expect(edits('f("x", "");')).toEqual([
      'StringLiteral: "x" → ""',
      'StringLiteral: "" → "Stryker was here!"',
    ]);
    expect(
      edits('import a from "a"; export * from "b"; const o = { "k": 1 }; require("c");')
    ).toEqual([]);
    expect(edits('"use strict";')).toEqual([]);
  });

  test("UpdateOperator, UnaryOperator, ArrayDeclaration, OptionalChaining, MethodExpression", () => {
    expect(edits("i++;")).toEqual(["UpdateOperator: ++ → --"]);
    expect(edits("f(-a);")).toEqual(["UnaryOperator: - → +"]);
    expect(edits("f([1]);")).toEqual(["ArrayDeclaration: [1] → []"]);
    expect(edits("f(a?.b);")).toEqual(["OptionalChaining: ?. → ."]);
    expect(edits("f(s.startsWith(t));")).toEqual(["MethodExpression: startsWith → endsWith"]);
  });
});

describe("what is never mutated", () => {
  test("type-only syntax", () => {
    const src = [
      'type T = "a" | "b";',
      'interface I { k: "x"; }',
      'let v: "lit" = g() as "lit";',
      "function h<U extends string = 'd'>(u: U): U { return u; }",
    ].join("\n");
    // Only the function body block survives the type filter.
    expect(edits(src)).toEqual(["BlockStatement: { return u; } → {}"]);
  });

  test("operator offsets are UTF-16, so text before a mutant can be non-ASCII", () => {
    const src = 'const s = "é—ü"; f(a === b);';
    const m = generateMutants("t.ts", src).mutants.find(
      (x) => x.mutatorName === "EqualityOperator"
    );
    expect(m && src.slice(m.start, m.end)).toBe("===");
  });
});

describe("verify primitives (polly#143)", () => {
  const src = 'requires(a === 1, "pre");\nverify.ensures(b, "post");\nf(c === 2);';

  test("mutants inside requires/ensures are kept but marked ignored, bare or as a member call", () => {
    const { mutants } = generateMutants("t.ts", src);
    const ignored = mutants.filter((m) => m.ignoredReason);
    expect(ignored.map((m) => m.location.start.line).sort()).toEqual([1, 1, 2]);
    expect(ignored[0]?.ignoredReason).toContain("polly#143");
    expect(mutants.filter((m) => !m.ignoredReason).map((m) => m.location.start.line)).toEqual([3]);
  });

  test("ignoreVerifyCallsites: false runs them like any other mutant", () => {
    const { mutants } = generateMutants("t.ts", src, { ignoreVerifyCallsites: false });
    expect(mutants.some((m) => m.ignoredReason)).toBe(false);
    expect(mutants.length).toBe(4);
  });
});

describe("ids, ranges, locations", () => {
  test("line ranges narrow the set and ids are prefixed and sequential", () => {
    const src = "f(a === b);\nf(c === d);\nf(e === g);";
    const { mutants } = generateMutants("t.ts", src, { lines: { from: 2, to: 3 }, idPrefix: "7." });
    expect(mutants.map((m) => m.id)).toEqual(["7.0", "7.1"]);
    expect(mutants.map((m) => m.location.start.line)).toEqual([2, 3]);
  });

  test("locations are 1-based line and column", () => {
    const pos = lineIndex("ab\ncd");
    expect(pos(0)).toEqual({ line: 1, column: 1 });
    expect(pos(4)).toEqual({ line: 2, column: 2 });
  });

  test("every generated mutant applies to a parseable program", () => {
    const src =
      "export function f(x: number) { if (x > 0 && !done) { return [x]; } return x?.y ?? -1; }";
    const { mutants, compileErrors } = generateMutants("t.ts", src);
    expect(compileErrors).toEqual([]);
    const applied = mutants.map((m: Mutant) => applyMutant(src, m));
    expect(new Set(applied).size).toBe(mutants.length);
  });

  test("an unparseable target is an error, not an empty set", () => {
    expect(() => generateMutants("t.ts", "function (")).toThrow("cannot parse target");
  });
});
