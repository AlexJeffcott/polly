import { afterAll, describe, expect, test } from "bun:test";
import { generateMutants } from "../engine/generate.ts";
import { HIT, instrument } from "../engine/probes.ts";
import { createFixtureProject } from "./fixture-project.ts";

/** The probed text, with each probe call shortened to `@n`. */
function probed(src: string): { code: string; probes: string[][] } {
  const { mutants } = generateMutants("t.ts", src);
  const out = instrument("t.ts", src, mutants, 0);
  if (!out) throw new Error("did not instrument");
  return { code: out.code.replaceAll(HIT, "@"), probes: out.probes };
}

describe("probe sites", () => {
  test("a statement in a list gets a probe before it", () => {
    expect(probed("f(a + b);\ng(c - d);").code).toBe(";@(0);f(a + b);\n;@(1);g(c - d);");
  });

  test("a lone statement is wrapped in a block", () => {
    expect(probed("if (a) f(b + c);").code).toBe(";@(0);if (a) {;@(1);f(b + c);}");
  });

  test("a function body block gets its own probe for the BlockStatement mutant", () => {
    const { code, probes } = probed("function f() { g(a + b); }");
    expect(code).toBe("function f() {;@(0); ;@(1);g(a + b); }");
    expect(probes[0]?.length).toBe(1);
  });

  test("arrow bodies, field values and defaults are wrapped as comma expressions", () => {
    expect(probed("const h = (v) => v - 1;").code).toBe(";@(0);const h = (v) => (@(1),v - 1);");
    expect(probed("class C { x = a + 1; }").code).toBe("class C { x = (@(0),a + 1); }");
    expect(probed('function f(s = "x") {}').code).toBe('function f(s = (@(0),"x")) {}');
  });

  test("an anonymous function value keeps its inferred name: no wrap", () => {
    expect(probed("class C { x = () => a + 1; }").code).toBe(
      ";@(0);class C { x = () => (@(1),a + 1); }"
    );
  });

  test("a directive keeps its place at the top of the prologue", () => {
    expect(probed('function f() { "use strict"; g(a + b); }').code).toBe(
      'function f() { "use strict";;@(0); ;@(1);g(a + b); }'
    );
  });

  test("a labelled loop body is not wrapped, so `continue label` still parses", () => {
    const { code } = probed("l: for (;;) { if (a > 1) continue l; }");
    expect(code).toContain("l: for (;;) {");
  });

  test("no line moves", () => {
    const src = "export function f(a: number) {\n  if (a > 1)\n    return a * 2;\n  return 0;\n}\n";
    expect(probed(src).code.split("\n").length).toBe(src.split("\n").length);
  });
});

describe("probed code behaves as the original", () => {
  const project = createFixtureProject("polly-mutate-probes-", {});
  afterAll(() => project.remove());

  test("results, function names and hits", async () => {
    const src = [
      '"use strict";',
      "export const LIMIT = 2 + 1;",
      "export function f(a = 1, { b = 2 } = {}) {",
      "  if (a > LIMIT) return a * 2;",
      "  for (const x of [1, 2]) a += x;",
      '  switch (a) { case 4: return "four"; default: break; }',
      "  return a ?? b;",
      "}",
      "export class C { x = 1 + 1; g = () => 3; m() { return this.x > 1 ? 'a' : 'b'; } }",
      "export const h = (v: number) => v - 1;",
    ].join("\n");
    const { mutants } = generateMutants("m.ts", src);
    const out = instrument("m.ts", src, mutants, 0);
    if (!out) throw new Error("did not instrument");
    const hits = new Set<number>();
    Reflect.set(globalThis, "__pollyMutateHit", (n: number) => hits.add(n));
    await Bun.write(project.path("orig.ts"), src);
    await Bun.write(project.path("probed.ts"), out.code);
    const orig = await import(project.path("orig.ts"));
    const mod = await import(project.path("probed.ts"));
    Reflect.deleteProperty(globalThis, "__pollyMutateHit");
    for (const args of [[], [9], [0], [1, { b: 5 }]])
      expect(mod.f(...args)).toEqual(orig.f(...args));
    expect(new mod.C().m()).toBe(new orig.C().m());
    expect(new mod.C().g.name).toBe("g");
    expect(mod.h(4)).toBe(3);
    expect(hits.size).toBeGreaterThan(0);
    expect(Math.max(...hits)).toBeLessThan(out.probes.length);
  });
});
