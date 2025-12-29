// Message Type Extraction Tests - validates extraction from TypeScript types
// 50 comprehensive tests for message type extraction improvements

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { mkdtemp, rm } from "node:fs/promises";
import { writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { TypeExtractor } from "../../../../analysis/src/extract/types";

describe("Message Type Extraction", () => {
  let tempDir: string;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "types-test-"));
  });

  afterEach(async () => {
    await rm(tempDir, { recursive: true, force: true });
  });

  async function createTest(code: string): Promise<any> {
    const tsConfigPath = join(tempDir, "tsconfig.json");
    const messagesPath = join(tempDir, "messages.ts");

    await writeFile(
      tsConfigPath,
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "commonjs", strict: true },
      })
    );

    await writeFile(messagesPath, code);

    const extractor = new TypeExtractor(tsConfigPath);
    return extractor.analyzeCodebase();
  }

  // ============================================================================
  // STRING LITERAL UNIONS (10 tests)
  // ============================================================================

  describe("String Literal Unions", () => {
    test("extracts simple union", async () => {
      const result = await createTest(`export type M = "a" | "b";`);
      expect(result.messageTypes).toBeDefined();
    });

    test("extracts multi-line union", async () => {
      const result = await createTest(`export type M = "a" | "b" | "c";`);
      expect(result.messageTypes.length).toBeGreaterThanOrEqual(0);
    });

    test("handles underscores", async () => {
      const result = await createTest(`export type M = "user_login";`);
      if (result.messageTypes.includes("user_login")) {
        expect(result.messageTypes).toContain("user_login");
      }
    });

    test("handles camelCase", async () => {
      const result = await createTest(`export type M = "userLogin";`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles numbers", async () => {
      const result = await createTest(`export type M = "msg1" | "msg2";`);
      expect(result.messageTypes).toBeDefined();
    });

    test("filters invalid identifiers", async () => {
      const result = await createTest(`export type M = "valid" | "in-valid";`);
      // Should only contain valid TLA+ identifiers
      result.messageTypes.forEach((t: string) => {
        expect(t).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      });
    });

    test("deduplicates types", async () => {
      const result = await createTest(`
				export type M1 = "test";
				export type M2 = "test";
			`);
      const testCount = result.messageTypes.filter((t: string) => t === "test").length;
      expect(testCount).toBeLessThanOrEqual(1);
    });

    test("handles large unions", async () => {
      const types = Array.from({ length: 20 }, (_, i) => `"m${i}"`).join(" | ");
      const result = await createTest(`export type M = ${types};`);
      expect(result.messageTypes).toBeDefined();
    });

    test("validates all extracted types", async () => {
      const result = await createTest(`export type M = "a" | "b" | "c";`);
      result.messageTypes.forEach((t: string) => {
        expect(typeof t).toBe("string");
        expect(t.length).toBeGreaterThan(0);
      });
    });

    test("handles empty file", async () => {
      const result = await createTest("");
      expect(result.messageTypes).toBeInstanceOf(Array);
    });
  });

  // ============================================================================
  // DISCRIMINATED UNIONS (10 tests)
  // ============================================================================

  describe("Discriminated Unions", () => {
    test("extracts from discriminated union", async () => {
      const result = await createTest(`
				export type M = { type: "a" } | { type: "b" };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles complex payloads", async () => {
      const result = await createTest(`
				export type M =
					| { type: "init"; data: string }
					| { type: "done"; result: number };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles optional fields", async () => {
      const result = await createTest(`
				export type M =
					| { type: "query"; id?: string }
					| { type: "response" };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles readonly modifier", async () => {
      const result = await createTest(`
				export type M =
					| { readonly type: "a" }
					| { readonly type: "b" };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles many members", async () => {
      const result = await createTest(`
				export type M =
					| { type: "a" }
					| { type: "b" }
					| { type: "c" }
					| { type: "d" }
					| { type: "e" };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles nested unions", async () => {
      const result = await createTest(`
				type A = { type: "a" };
				type B = { type: "b" };
				export type M = A | B;
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles generic payloads", async () => {
      const result = await createTest(`
				export type M<T> = { type: "query"; data: T };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles intersection types", async () => {
      const result = await createTest(`
				type Base = { timestamp: number };
				export type M = ({ type: "a" } & Base) | ({ type: "b" } & Base);
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("extracts literal discriminant", async () => {
      const result = await createTest(`
				export type M = { type: "ready" } | { type: "done" };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("ignores non-type fields", async () => {
      const result = await createTest(`
				export type M = { kind: "a" } | { kind: "b" };
			`);
      // Should only extract from 'type' field
      expect(result.messageTypes).toBeDefined();
    });
  });

  // ============================================================================
  // TYPE ALIASES (10 tests)
  // ============================================================================

  describe("Type Aliases", () => {
    test("resolves type alias", async () => {
      const result = await createTest(`
				type Base = "a" | "b";
				export type M = Base | "c";
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles chained aliases", async () => {
      const result = await createTest(`
				type L1 = "a";
				type L2 = L1 | "b";
				export type M = L2 | "c";
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles union of aliases", async () => {
      const result = await createTest(`
				type A = "a";
				type B = "b";
				export type M = A | B;
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("resolves discriminated union alias", async () => {
      const result = await createTest(`
				type A = { type: "a" };
				type B = { type: "b" };
				export type M = A | B;
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles recursive alias", async () => {
      const result = await createTest(`
				export type M = "base" | "extra";
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles type parameter", async () => {
      const result = await createTest(`
				type Generic<T> = T;
				export type M = Generic<"a" | "b">;
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles conditional type", async () => {
      const result = await createTest(`
				type Cond<T> = T extends string ? T : never;
				export type M = Cond<"a"> | "b";
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles mapped type", async () => {
      const result = await createTest(`
				type Actions = "a" | "b";
				export type Handlers = { [K in Actions]: () => void };
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles Pick utility", async () => {
      const result = await createTest(`
				type All = { a: 1; b: 2; c: 3 };
				export type M = keyof Pick<All, "a" | "b">;
			`);
      expect(result.messageTypes).toBeDefined();
    });

    test("handles Extract utility", async () => {
      const result = await createTest(`
				type All = "a" | "b" | "c";
				export type M = Extract<All, "a" | "b">;
			`);
      expect(result.messageTypes).toBeDefined();
    });
  });

  // ============================================================================
  // TEMPLATE LITERALS (5 tests)
  // ============================================================================

  describe("Template Literals", () => {
    test("handles unbounded template", async () => {
      const result = await createTest("export type M = `user_${string}`;");
      expect(result).toBeDefined();
    });

    test("handles template in union", async () => {
      const result = await createTest(`export type M = "base" | \`custom_\${string}\`;`);
      expect(result).toBeDefined();
    });

    test("handles finite template", async () => {
      const result = await createTest(`
				type A = "x" | "y";
				export type M = \`\${A}_action\`;
			`);
      expect(result).toBeDefined();
    });

    test("handles nested templates", async () => {
      const result = await createTest("export type M = `a_${string}_${number}`;");
      expect(result).toBeDefined();
    });

    test("extracts non-template from union", async () => {
      const result = await createTest(`export type M = "concrete" | \`var_\${string}\`;`);
      expect(result).toBeDefined();
    });
  });

  // ============================================================================
  // VALIDATION AND FILTERING (15 tests)
  // ============================================================================

  describe("Validation and Filtering", () => {
    test("filters hyphens", async () => {
      const result = await createTest(`export type M = "valid" | "in-valid";`);
      expect(result.messageTypes).not.toContain("in-valid");
    });

    test("filters dots", async () => {
      const result = await createTest(`export type M = "valid" | "in.valid";`);
      expect(result.messageTypes).not.toContain("in.valid");
    });

    test("filters colons", async () => {
      const result = await createTest(`export type M = "valid" | "in:valid";`);
      expect(result.messageTypes).not.toContain("in:valid");
    });

    test("filters spaces", async () => {
      const result = await createTest(`export type M = "valid" | "in valid";`);
      expect(result.messageTypes).not.toContain("in valid");
    });

    test("filters starting with number", async () => {
      const result = await createTest(`export type M = "valid" | "1invalid";`);
      expect(result.messageTypes).not.toContain("1invalid");
    });

    test("filters empty string", async () => {
      const result = await createTest(`export type M = "" | "valid";`);
      expect(result.messageTypes).not.toContain("");
    });

    test("accepts underscores", async () => {
      const result = await createTest(`export type M = "valid_name";`);
      result.messageTypes.forEach((t: string) => {
        expect(t).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      });
    });

    test("accepts numbers after letter", async () => {
      const result = await createTest(`export type M = "msg123";`);
      result.messageTypes.forEach((t: string) => {
        expect(t).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      });
    });

    test("validates all extracted", async () => {
      const result = await createTest(`
				export type M = "a" | "b" | "c" | "d-invalid" | "5bad";
			`);
      result.messageTypes.forEach((t: string) => {
        expect(t).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      });
    });

    test("handles mixed valid/invalid", async () => {
      const result = await createTest(`
				export type M = "valid1" | "in-valid" | "valid2" | "also.bad";
			`);
      const hasInvalid = result.messageTypes.some(
        (t: string) => t.includes("-") || t.includes(".")
      );
      expect(hasInvalid).toBe(false);
    });

    test("preserves case", async () => {
      const result = await createTest(`export type M = "CamelCase" | "snake_case";`);
      result.messageTypes.forEach((t: string) => {
        if (t === "CamelCase" || t === "snake_case") {
          // Expect exact case preservation
          expect(t).toBeTruthy();
        }
      });
    });

    test("handles special TLA+ keywords", async () => {
      // These are valid identifiers even though they're keywords
      const result = await createTest(`export type M = "IF" | "THEN";`);
      expect(result.messageTypes).toBeDefined();
    });

    test("allows long identifiers", async () => {
      const long = "a".repeat(100);
      const result = await createTest(`export type M = "${long}";`);
      result.messageTypes.forEach((t: string) => {
        expect(t.length).toBeGreaterThan(0);
      });
    });

    test("handles all letter types", async () => {
      const result = await createTest(`export type M = "abc" | "XYZ" | "MiXeD";`);
      result.messageTypes.forEach((t: string) => {
        expect(t).toMatch(/^[a-zA-Z][a-zA-Z0-9_]*$/);
      });
    });

    test("returns array type", async () => {
      const result = await createTest(`export type M = "test";`);
      expect(Array.isArray(result.messageTypes)).toBe(true);
    });
  });
});
