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
    expect(edits("f(a < b);")).toEqual([
      "ConditionalExpression: a < b → true",
      "ConditionalExpression: a < b → false",
      "EqualityOperator: < → <=",
      "EqualityOperator: < → >=",
    ]);
    expect(edits("f(a === b);").filter((e) => e.startsWith("Equality"))).toEqual([
      "EqualityOperator: === → !==",
    ]);
  });

  test("ArithmeticOperator skips concatenation, judged as Stryker does", () => {
    expect(edits("f(a + b);")).toEqual(["ArithmeticOperator: + → -"]);
    expect(edits('f("x" + b);')).toEqual(['StringLiteral: "x" → ""']);
    // The outer `+` has a binary left whose right operand is a string.
    expect(edits('f(a + "x" + b);')).toEqual(['StringLiteral: "x" → ""']);
    expect(edits('f("x" - b);')).toEqual(['StringLiteral: "x" → ""']);
  });

  test("LogicalOperator", () => {
    expect(edits("f(a && b);")).toContain("LogicalOperator: && → ||");
    expect(edits("f(a ?? b);")).toEqual(["LogicalOperator: a ?? b → (a && b)"]);
  });

  test("a ?? chain mutates to a parseable expression", () => {
    const { mutants, compileErrors } = generateMutants("t.ts", "f(a ?? b ?? c);");
    expect(compileErrors).toEqual([]);
    expect(mutants.map((m) => m.replacement)).toEqual(["(a && b)", "((a ?? b) && c)"]);
  });

  test("AssignmentOperator, except a concatenating assignment of a string", () => {
    expect(edits("x += 1;")).toEqual(["AssignmentOperator: += → -="]);
    expect(edits("x >>= 2;")).toEqual(["AssignmentOperator: >>= → <<="]);
    expect(edits("x ??= y;")).toEqual(["AssignmentOperator: ??= → &&="]);
    expect(edits('x += "s";')).toEqual(['StringLiteral: "s" → ""']);
    expect(edits('x ||= "s";')).toEqual([
      "AssignmentOperator: ||= → &&=",
      'StringLiteral: "s" → ""',
    ]);
  });

  test("BooleanLiteral flips literals and drops logical not", () => {
    expect(edits("f(true);")).toEqual(["BooleanLiteral: true → false"]);
    expect(edits("f(!a);")).toEqual(["BooleanLiteral: ! → "]);
  });

  test("operators next to parentheses keep them (parens are not in any node's span)", () => {
    const applied = (src: string, mutator: string) => {
      const { mutants, compileErrors } = generateMutants("t.ts", src);
      expect(compileErrors).toEqual([]);
      return mutants.filter((m) => m.mutatorName === mutator).map((m) => applyMutant(src, m));
    };
    expect(applied("f(!(a in b));", "BooleanLiteral")).toEqual(["f((a in b));"]);
    expect(applied("f(-(a));", "UnaryOperator")).toEqual(["f(+(a));"]);
    expect(applied("f(a ?? (b as T));", "LogicalOperator")).toEqual(["f((a && (b as T)));"]);
    expect(applied("f((a) ?? b ?? (c ? 1 : 2));", "LogicalOperator")).toEqual([
      "f(((a) && b) ?? (c ? 1 : 2));",
      "f((((a) ?? b) && (c ? 1 : 2)));",
    ]);
  });

  test("ConditionalExpression: if tests both ways, loop tests false only", () => {
    expect(edits("if (a) g();")).toEqual([
      "ConditionalExpression: a → true",
      "ConditionalExpression: a → false",
    ]);
    expect(edits("while (a < 1) g();")).toEqual([
      "ConditionalExpression: a < 1 → false",
      "EqualityOperator: < → <=",
      "EqualityOperator: < → >=",
    ]);
  });

  test("ConditionalExpression: a ternary test only when it is a boolean expression", () => {
    expect(edits("x = a ? 1 : 2;")).toEqual([]);
    expect(edits("x = a > 1 ? 1 : 2;").slice(0, 2)).toEqual([
      "ConditionalExpression: a > 1 → true",
      "ConditionalExpression: a > 1 → false",
    ]);
  });

  test("ConditionalExpression: an operand of || is only forced false, of && only true", () => {
    const or = edits("f(a || b < c);").filter((e) => e.startsWith("ConditionalExpression: b"));
    const and = edits("f(a && b < c);").filter((e) => e.startsWith("ConditionalExpression: b"));
    expect(or).toEqual(["ConditionalExpression: b < c → false"]);
    expect(and).toEqual(["ConditionalExpression: b < c → true"]);
  });

  test("ConditionalExpression: a test-less for gets `false`, a non-fallthrough case is emptied", () => {
    const src = "for (let i = 0;; i++) g();";
    const m = generateMutants("t.ts", src).mutants.find(
      (x) => x.mutatorName === "ConditionalExpression"
    );
    expect(m && applyMutant(src, m)).toBe("for (let i = 0;false; i++) g();");
    expect(edits("switch (k) { case 1: g(); break; case 2: case 3: h(); }")).toEqual([
      "ConditionalExpression: g(); break; → ",
      "ConditionalExpression: h(); → ",
    ]);
  });

  test("BlockStatement keeps a super() constructor only when emptying it would not compile", () => {
    expect(edits("function f() { g(); }")).toEqual(["BlockStatement: { g(); } → {}"]);
    const block = "BlockStatement: { super(); } → {}";
    expect(edits("class B extends A { constructor() { super(); } }")).toEqual([block]);
    expect(edits("class B extends A { #x = 1; constructor() { super(); } }")).toEqual([block]);
    expect(edits("class B extends A { x = 1; constructor() { super(); } }")).toEqual([]);
    expect(edits("class B extends A { constructor(private y = 1) { super(); } }")).toEqual([]);
  });

  test("StringLiteral replaces values, not names or module specifiers", () => {
    expect(edits('f("x", "");')).toEqual([
      'StringLiteral: "x" → ""',
      'StringLiteral: "" → "Stryker was here!"',
    ]);
    expect(
      edits(
        'import a from "a"; export * from "b"; export default "z"; import("m"); require("c"); Symbol("s");'
      )
    ).toEqual([]);
    expect(edits('const o = { "k": 1, ["c"]: 2 };')).toEqual([
      'ObjectLiteral: { "k": 1, ["c"]: 2 } → {}',
    ]);
    expect(edits('"use strict";')).toEqual([]);
    // A quoted method name is a value to Stryker (it only spares property keys).
    expect(edits('class C { "m"() {} p = "v"; }')).toEqual([
      'StringLiteral: "m" → ""',
      'StringLiteral: "v" → ""',
    ]);
  });

  test("StringLiteral skips JSX attribute values but not JSX expression strings", () => {
    expect(edits('<a href="x">{"y"}</a>;', "t.tsx")).toEqual(['StringLiteral: "y" → ""']);
  });

  test("StringLiteral empties template literals, tagged ones too", () => {
    // biome-ignore lint/suspicious/noTemplateCurlyInString: the template is source text under test
    expect(edits("f(`a${b}`);")).toEqual(["StringLiteral: `a${b}` → ``"]);
    expect(edits("f(``);")).toEqual(["StringLiteral: `` → `Stryker was here!`"]);
    expect(edits("f(tag`x`);")).toEqual(["StringLiteral: `x` → ``"]);
  });

  test("Regex: weapon-regex level 1 on literals and on new RegExp's pattern", () => {
    expect(edits("f(/a+/g);")).toEqual(["Regex: /a+/g → /a/g"]);
    expect(edits('f(new RegExp("\\\\d+", "i"));').filter((e) => e.startsWith("Regex"))).toEqual([
      'Regex: "\\\\d+" → "\\\\d"',
      'Regex: "\\\\d+" → "\\\\D+"',
    ]);
    expect(edits('f(RegExp("a+"));')).toEqual(['StringLiteral: "a+" → ""']);
  });

  test("ObjectLiteral and ArrowFunction", () => {
    expect(edits("f({ a: 1 });")).toEqual(["ObjectLiteral: { a: 1 } → {}"]);
    expect(edits("f({});")).toEqual([]);
    expect(edits("const g = () => x;")).toEqual(["ArrowFunction: () => x → () => undefined"]);
    expect(edits("const g = () => undefined;")).toEqual([]);
    expect(edits("const g = () => { return x; };")).toEqual(["BlockStatement: { return x; } → {}"]);
  });

  test("ArrayDeclaration on literals and Array() calls", () => {
    expect(edits("f([1]);")).toEqual(["ArrayDeclaration: [1] → []"]);
    expect(edits("f([]);")).toEqual(['ArrayDeclaration: [] → ["Stryker was here"]']);
    expect(edits("f(new Array(1, 2));")).toEqual([
      "ArrayDeclaration: new Array(1, 2) → new Array()",
    ]);
    expect(edits("f(Array());")).toEqual(["ArrayDeclaration: Array() → Array([])"]);
  });

  test("MethodExpression swaps pairs both ways and drops filtering calls", () => {
    expect(edits("f(s.startsWith(t));")).toEqual(["MethodExpression: startsWith → endsWith"]);
    expect(edits("f(d.setMinutes(1));")).toEqual(["MethodExpression: setMinutes → setHours"]);
    // setUTCDate → setTime is one-way; setTime reverses to setDate.
    expect(edits("f(d.setTime(1));")).toEqual(["MethodExpression: setTime → setDate"]);
    expect(edits("f(a.filter(x));")).toEqual(["MethodExpression: a.filter(x) → a"]);
    expect(edits("f(a?.trim());")).toEqual([
      "MethodExpression: a?.trim() → a",
      "OptionalChaining: ?. → .",
    ]);
  });

  test("UpdateOperator, UnaryOperator, OptionalChaining", () => {
    expect(edits("i++;")).toEqual(["UpdateOperator: ++ → --"]);
    expect(edits("f(-a);")).toEqual(["UnaryOperator: - → +"]);
    expect(edits("f(a?.b);")).toEqual(["OptionalChaining: ?. → ."]);
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

  test("decorators and declare statements, as Stryker skips them", () => {
    expect(edits('@dec("x") class D { m() { g(); } }')).toEqual(["BlockStatement: { g(); } → {}"]);
    expect(edits('declare const q: "a";')).toEqual([]);
  });

  test("runtime code under TS syntax is still mutated", () => {
    expect(edits("namespace N { export const v = 1 + 2; }")).toEqual(["ArithmeticOperator: + → -"]);
    expect(edits("f(<T>(a + b));")).toEqual(["ArithmeticOperator: + → -"]);
    expect(edits("class K { constructor(private y = 1 + 2) {} }")).toEqual([
      "ArithmeticOperator: + → -",
    ]);
    // Stryker skips everything under `as`; this engine mutates the expression (README).
    expect(edits("f((a + b) as T);")).toEqual(["ArithmeticOperator: + → -"]);
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
    expect(ignored.map((m) => m.location.start.line).sort()).toEqual([1, 1, 1, 1, 2]);
    expect(ignored[0]?.ignoredReason).toContain("polly#143");
    expect(mutants.filter((m) => !m.ignoredReason).map((m) => m.location.start.line)).toEqual([
      3, 3, 3,
    ]);
  });

  test("ignoreVerifyCallsites: false runs them like any other mutant", () => {
    const { mutants } = generateMutants("t.ts", src, { ignoreVerifyCallsites: false });
    expect(mutants.some((m) => m.ignoredReason)).toBe(false);
    expect(mutants.length).toBe(8);
  });
});

describe("ids, ranges, locations", () => {
  test("line ranges narrow the set and ids are prefixed and sequential", () => {
    const src = "f(a + b);\nf(c + d);\nf(e + g);";
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

describe("exclude", () => {
  test("an excluded mutator generates nothing; the others are unchanged", () => {
    const src = 'const s = a > 1 ? "x" : "y";';
    const names = (exclude: Parameters<typeof generateMutants>[2]) =>
      new Set(generateMutants("t.ts", src, exclude).mutants.map((m) => m.mutatorName));
    const all = names({});
    expect(all.has("StringLiteral")).toBe(true);
    const without = names({ exclude: ["StringLiteral"] });
    expect(without.has("StringLiteral")).toBe(false);
    expect([...without]).toEqual([...all].filter((n) => n !== "StringLiteral"));
  });
});
