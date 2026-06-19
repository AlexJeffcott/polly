import { describe, expect, test } from "bun:test";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  checkNoTautologyEnsures,
  splitTopLevelArgs,
  tautologyReason,
} from "../../tools/quality/src/no-tautology-ensures";

describe("tautologyReason — flagged predicates", () => {
  test("literal true", () => {
    expect(tautologyReason("true")).toContain("literal");
  });
  test("literal false", () => {
    expect(tautologyReason("false")).toContain("literal");
  });
  test("null / undefined", () => {
    expect(tautologyReason("null")).toBeDefined();
    expect(tautologyReason("undefined")).toBeDefined();
  });
  test("numeric literal", () => {
    expect(tautologyReason("42")).toBeDefined();
    expect(tautologyReason("3.14")).toBeDefined();
  });
  test("string literal", () => {
    expect(tautologyReason("'hi'")).toBeDefined();
    expect(tautologyReason('"hi"')).toBeDefined();
  });
  test("literal-vs-literal comparison", () => {
    expect(tautologyReason("1 === 1")).toContain("literal-vs-literal");
    expect(tautologyReason("'a' !== 'b'")).toContain("literal-vs-literal");
  });
});

describe("tautologyReason — real predicates pass", () => {
  test("identifier reference", () => {
    expect(tautologyReason("state.connected")).toBeUndefined();
  });
  test("comparison against state", () => {
    expect(tautologyReason("state.count === 1")).toBeUndefined();
  });
  test("negation of state", () => {
    expect(tautologyReason("!state.loading")).toBeUndefined();
  });
  test("call expression", () => {
    expect(tautologyReason("isReady(state)")).toBeUndefined();
  });
});

describe("splitTopLevelArgs", () => {
  test("splits on top-level commas only", () => {
    expect(splitTopLevelArgs("a, b, c")).toEqual(["a", "b", "c"]);
  });
  test("ignores commas inside nesting and strings", () => {
    expect(splitTopLevelArgs("fn(a, b), 'x, y'")).toEqual(["fn(a, b)", "'x, y'"]);
  });
});

describe("checkNoTautologyEnsures — integration", () => {
  function fixture(files: Record<string, string>): string {
    const dir = mkdtempSync(join(tmpdir(), "no-tautology-"));
    for (const [name, content] of Object.entries(files)) {
      writeFileSync(join(dir, name), content);
    }
    return dir;
  }

  test("flags ensures(true) and requires(literal)", async () => {
    const dir = fixture({
      "a.ts": "ensures(true, 'always');\nrequires(state.ready, 'ready');\n",
      "b.ts": "requires(1 === 1, 'tautology');\n",
    });
    const { violations } = await checkNoTautologyEnsures({ rootDir: dir });
    expect(violations).toHaveLength(2);
    expect(violations.map((v) => v.file).sort()).toEqual(["a.ts", "b.ts"]);
  });

  test("passes when every predicate references state", async () => {
    const dir = fixture({
      "ok.ts": "ensures(state.value === next, 'set');\nrequires(handle != null, 'present');\n",
    });
    const { violations } = await checkNoTautologyEnsures({ rootDir: dir });
    expect(violations).toHaveLength(0);
  });

  test("ignores import lines and comments", async () => {
    const dir = fixture({
      "imp.ts":
        "import { ensures, requires } from '@fairfox/polly/verify';\n// ensures(true) in a comment\n",
    });
    const { violations } = await checkNoTautologyEnsures({ rootDir: dir });
    expect(violations).toHaveLength(0);
  });

  test("respects a custom primitive set", async () => {
    const dir = fixture({ "inv.ts": "invariant(true, 'x');\n" });
    const base = await checkNoTautologyEnsures({ rootDir: dir });
    expect(base.violations).toHaveLength(0);
    const wide = await checkNoTautologyEnsures({ rootDir: dir, primitives: ["invariant"] });
    expect(wide.violations).toHaveLength(1);
  });
});
