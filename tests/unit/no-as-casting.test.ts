import { describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkNoAsCasting, isLineClean } from "../../tools/quality/src/no-as-casting";

describe("isLineClean — allowed patterns", () => {
  test("no `as` keyword at all", () => {
    expect(isLineClean("const x: number = 42;")).toBe(true);
  });

  test("as const", () => {
    expect(isLineClean("const x = [1, 2, 3] as const;")).toBe(true);
  });

  test("as unknown as (escape hatch)", () => {
    expect(isLineClean("const x = y as unknown as string;")).toBe(true);
  });

  test("import rename", () => {
    expect(isLineClean("import { X as Y } from './mod';")).toBe(true);
  });

  test("export rename", () => {
    expect(isLineClean("export { Foo as Bar } from './mod';")).toBe(true);
  });

  test("import * as namespace", () => {
    expect(isLineClean("import * as path from 'node:path';")).toBe(true);
  });

  test("import type rename", () => {
    expect(isLineClean("import type { Foo as Bar } from './mod';")).toBe(true);
  });

  test("destructured rename in import block", () => {
    expect(isLineClean("  Foo as Bar,")).toBe(true);
  });

  test("property declaration with as=", () => {
    expect(isLineClean('<Component as="div" />')).toBe(true);
  });

  test("property declaration with as:", () => {
    expect(isLineClean("  as: 'button',")).toBe(true);
  });

  test("satisfies keyword", () => {
    expect(isLineClean("const config = {} satisfies Config as any;")).toBe(true);
  });

  test("full-line comment with //", () => {
    expect(isLineClean("  // cast this as string")).toBe(true);
  });

  test("full-line comment with /*", () => {
    expect(isLineClean("  /* treated as string */")).toBe(true);
  });

  test("block comment continuation with *", () => {
    expect(isLineClean("   * used as a fallback")).toBe(true);
  });

  test("inline comment after clean code", () => {
    expect(isLineClean("const x = 1; // treated as string")).toBe(true);
  });
});

describe("isLineClean — string literals (#45)", () => {
  test("single-quoted string containing ` as `", () => {
    expect(isLineClean("const msg = 'Output as JSON';")).toBe(true);
  });

  test("double-quoted string containing ` as `", () => {
    expect(isLineClean('const msg = "Output as JSON";')).toBe(true);
  });

  test("backtick template literal containing ` as `", () => {
    expect(isLineClean("const msg = `Output as JSON`;")).toBe(true);
  });

  test("CLI help text in template literal", () => {
    expect(isLineClean("  --json               Output as JSON")).toBe(true);
  });

  test("template literal body with --apply flag", () => {
    expect(isLineClean("  --apply              Apply suggestions as drafts")).toBe(true);
  });

  test("instruction text with ` as `", () => {
    expect(isLineClean("- Use --apply to save the suggestion as a draft value")).toBe(true);
  });

  test("tone instruction text", () => {
    expect(isLineClean("- Maintain the same tone and formality level as the source")).toBe(true);
  });
});

describe("isLineClean — JSX text (#45)", () => {
  test("JSX text with ` as ` between tags", () => {
    expect(isLineClean("This text renders as a paragraph element.")).toBe(true);
  });

  test("JSX text with prose-like content", () => {
    expect(isLineClean("      Use this value as the default setting")).toBe(true);
  });
});

describe("isLineClean — SQL aliases (#45)", () => {
  test("SQL column alias in string", () => {
    expect(isLineClean('") as column_name"')).toBe(true);
  });
});

describe("isLineClean — violations (must detect)", () => {
  test("simple type assertion", () => {
    expect(isLineClean("const x = y as string;")).toBe(false);
  });

  test("type assertion with complex type", () => {
    expect(isLineClean("const el = document.getElementById('x') as HTMLDivElement;")).toBe(false);
  });

  test("as any", () => {
    expect(isLineClean("return value as any;")).toBe(false);
  });

  test("JSON.parse with cast", () => {
    expect(isLineClean("const data = JSON.parse(raw) as MyType;")).toBe(false);
  });

  test("branded type cast", () => {
    expect(isLineClean('const id = "abc" as PeerId;')).toBe(false);
  });
});

describe("checkNoAsCasting — excludePackages (#44)", () => {
  test("skips files in excluded packages", async () => {
    const dir = mkdtempSync(join(tmpdir(), "polly-quality-"));
    mkdirSync(join(dir, "legacy-pkg", "src"), { recursive: true });
    mkdirSync(join(dir, "good-pkg", "src"), { recursive: true });
    writeFileSync(join(dir, "legacy-pkg", "src", "a.ts"), "const x = y as string;\n");
    writeFileSync(join(dir, "good-pkg", "src", "b.ts"), "const x = y as string;\n");

    const result = await checkNoAsCasting({
      rootDir: dir,
      excludePackages: ["legacy-pkg"],
    });

    expect(result.violations.length).toBe(1);
    expect(result.violations[0]?.file).toContain("good-pkg");
  });
});

describe("checkNoAsCasting — excludeFiles (#44)", () => {
  test("skips files matching basename", async () => {
    const dir = mkdtempSync(join(tmpdir(), "polly-quality-"));
    writeFileSync(join(dir, "relay.ts"), "const x = y as string;\n");
    writeFileSync(join(dir, "app.ts"), "const x = y as string;\n");

    const result = await checkNoAsCasting({
      rootDir: dir,
      excludeFiles: ["relay.ts"],
    });

    expect(result.violations.length).toBe(1);
    expect(result.violations[0]?.file).toBe("app.ts");
  });

  test("skips files matching relative path", async () => {
    const dir = mkdtempSync(join(tmpdir(), "polly-quality-"));
    mkdirSync(join(dir, "scripts"), { recursive: true });
    writeFileSync(join(dir, "scripts", "migrate.ts"), "const x = y as string;\n");
    writeFileSync(join(dir, "app.ts"), "const x = y as string;\n");

    const result = await checkNoAsCasting({
      rootDir: dir,
      excludeFiles: ["scripts/migrate.ts"],
    });

    expect(result.violations.length).toBe(1);
    expect(result.violations[0]?.file).toBe("app.ts");
  });
});
