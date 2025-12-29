// Tests for invariant extraction from JSDoc annotations

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { InvariantExtractor, InvariantGenerator } from "../../codegen/invariants";

describe("Invariant Extraction", () => {
  const tempDirs: string[] = [];

  const createTempProject = (files: Record<string, string>): string => {
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "polly-invariants-test-"));
    tempDirs.push(tempDir);

    // Create tsconfig.json
    fs.writeFileSync(
      path.join(tempDir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: {
          target: "ES2020",
          module: "commonjs",
          strict: true,
        },
      })
    );

    // Create source files
    for (const [filename, content] of Object.entries(files)) {
      fs.writeFileSync(path.join(tempDir, filename), content);
    }

    return tempDir;
  };

  // Cleanup on exit
  process.on("exit", () => {
    for (const dir of tempDirs) {
      if (fs.existsSync(dir)) {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    }
  });

  // ============================================================================
  // Basic Extraction Tests (10 tests)
  // ============================================================================

  test("extracts simple @invariant tag", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count >= 0
 */
function increment(state: any) {
  state.count++;
}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0");
    expect(result.invariants[0]?.name).toContain("Count");
  });

  test("extracts @ensures tag as post-condition", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @ensures state.count > 0
 */
function setPositive(state: any) {
  state.count = 1;
}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count > 0");
    expect(result.invariants[0]?.name).toContain("Post");
  });

  test("extracts @requires tag as pre-condition", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @requires state.count >= 0
 */
function decrement(state: any) {
  state.count--;
}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0");
    expect(result.invariants[0]?.name).toContain("Pre");
  });

  test("extracts multiple invariants from single file", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count >= 0
 * @invariant state.count <= 100
 */
function update(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(2);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0");
    expect(result.invariants[1]?.expression).toBe("state.count <= 100");
  });

  test("extracts invariants with descriptions", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * Maximum 100 items allowed
 * @invariant state.items.length <= 100
 */
function addItem(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.description).toContain("Maximum 100 items");
  });

  test("skips test files", () => {
    const projectPath = createTempProject({
      "test.test.ts": `
/**
 * @invariant state.count >= 0
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(0);
  });

  test("skips node_modules", () => {
    // Create empty project first
    const projectPath = createTempProject({});

    // Create node_modules directory with invariant annotation
    const nodeModulesDir = path.join(projectPath, "node_modules", "pkg");
    fs.mkdirSync(nodeModulesDir, { recursive: true });
    fs.writeFileSync(
      path.join(nodeModulesDir, "index.ts"),
      "/** @invariant x > 0 */ export function test() {}"
    );

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    // Should skip node_modules
    expect(result.invariants).toHaveLength(0);
  });

  test("extracts from class methods", () => {
    const projectPath = createTempProject({
      "test.ts": `
class Counter {
  /**
   * @invariant state.count >= 0
   */
  increment(state: any) {}
}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0");
  });

  test("extracts from arrow functions", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count >= 0
 */
const increment = (state: any) => {
  state.count++;
};
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0");
  });

  test("extracts from variable declarations", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant MAX_COUNT > 0
 */
const MAX_COUNT = 100;
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("MAX_COUNT > 0");
  });

  // ============================================================================
  // Expression Complexity Tests (10 tests)
  // ============================================================================

  test("handles compound expressions with &&", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count >= 0 && state.count <= 100
 */
function update(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count >= 0 && state.count <= 100");
  });

  test("handles expressions with ||", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.status === "active" || state.status === "pending"
 */
function process(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toContain("||");
  });

  test("handles negation with !", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant !state.locked
 */
function unlock(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("!state.locked");
  });

  test("handles implication with =>", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.processing === true => state.lock === true
 */
function process(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toContain("=>");
  });

  test("handles array length checks", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.items.length <= 100
 */
function addItem(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.items.length <= 100");
  });

  test("handles nested property access", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.user.profile.age >= 18
 */
function updateProfile(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.user.profile.age >= 18");
  });

  test("handles parenthesized expressions", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant (state.a + state.b) === state.total
 */
function calculate(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toContain("(state.a + state.b)");
  });

  test("handles strict equality operators", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count === 0
 */
function reset(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count === 0");
  });

  test("handles inequality operators", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.status !== "error"
 */
function process(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe('state.status !== "error"');
  });

  test("handles multiple state references", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count <= state.maxCount
 */
function increment(state: any) {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants).toHaveLength(1);
    expect(result.invariants[0]?.expression).toBe("state.count <= state.maxCount");
  });

  // ============================================================================
  // Name Generation Tests (5 tests)
  // ============================================================================

  test("generates name for >= constraint", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count >= 0
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants[0]?.name).toBe("CountMinValue");
  });

  test("generates name for <= constraint", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.count <= 100
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants[0]?.name).toBe("CountMaxValue");
  });

  test("generates name for === constraint", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @invariant state.status === "active"
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants[0]?.name).toBe("StatusEquals");
  });

  test("generates name for pre-condition", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @requires state.count > 0
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants[0]?.name).toContain("Pre");
    expect(result.invariants[0]?.name).toContain("Count");
  });

  test("generates name for post-condition", () => {
    const projectPath = createTempProject({
      "test.ts": `
/**
 * @ensures state.done === true
 */
function test() {}
`,
    });

    const extractor = new InvariantExtractor();
    const result = extractor.extractInvariants(projectPath);

    expect(result.invariants[0]?.name).toContain("Post");
    expect(result.invariants[0]?.name).toContain("Done");
  });

  // ============================================================================
  // Validation Tests (5 tests)
  // ============================================================================

  test("validates expressions with balanced parentheses", () => {
    const extractor = new InvariantExtractor();

    const result = extractor.validateExpression("(state.a + state.b) === state.total");

    expect(result.valid).toBe(true);
  });

  test("rejects expressions with unbalanced parentheses", () => {
    const extractor = new InvariantExtractor();

    const result = extractor.validateExpression("(state.a + state.b === state.total");

    expect(result.valid).toBe(false);
    expect(result.error).toContain("parentheses");
  });

  test("rejects expressions with unbalanced brackets", () => {
    const extractor = new InvariantExtractor();

    const result = extractor.validateExpression("state.items[0.length > 0");

    expect(result.valid).toBe(false);
    expect(result.error).toContain("brackets");
  });

  test("rejects expressions with eval()", () => {
    const extractor = new InvariantExtractor();

    const result = extractor.validateExpression("eval('state.count > 0')");

    expect(result.valid).toBe(false);
    expect(result.error).toContain("eval");
  });

  test("validates complex valid expressions", () => {
    const extractor = new InvariantExtractor();

    const result = extractor.validateExpression(
      "state.count >= 0 && state.count <= 100 && state.items.length > 0"
    );

    expect(result.valid).toBe(true);
  });
});

describe("Invariant Generation", () => {
  const mockTranslate = (expr: string): string => {
    // Simple mock translation for testing
    return expr
      .replace(/state\./g, "contextStates[ctx].")
      .replace(/&&/g, "/\\")
      .replace(/\|\|/g, "\\/")
      .replace(/===/g, "=")
      .replace(/!==/g, "#");
  };

  test("generates TLA+ invariant with universal quantifier", () => {
    const invariant = {
      name: "CountMinValue",
      description: "Count must be non-negative",
      expression: "state.count >= 0",
      location: { file: "test.ts", line: 1 },
    };

    const generator = new InvariantGenerator();
    const tla = generator.generateTLAInvariants([invariant], mockTranslate);

    expect(tla).toHaveLength(1);
    expect(tla[0]).toContain("CountMinValue ==");
    expect(tla[0]).toContain("\\A ctx \\in Contexts");
    expect(tla[0]).toContain("contextStates[ctx].count >= 0");
  });

  test("includes description as comment", () => {
    const invariant = {
      name: "CountMaxValue",
      description: "Maximum 100 allowed",
      expression: "state.count <= 100",
      location: { file: "test.ts", line: 1 },
    };

    const generator = new InvariantGenerator();
    const tla = generator.generateTLAInvariants([invariant], mockTranslate);

    expect(tla[0]).toContain("\\* Maximum 100 allowed");
  });

  test("translates compound expressions", () => {
    const invariant = {
      name: "CountRange",
      description: "Count in valid range",
      expression: "state.count >= 0 && state.count <= 100",
      location: { file: "test.ts", line: 1 },
    };

    const generator = new InvariantGenerator();
    const tla = generator.generateTLAInvariants([invariant], mockTranslate);

    expect(tla[0]).toContain("/\\");
    expect(tla[0]).not.toContain("&&");
  });

  test("generates config file invariant declarations", () => {
    const invariants = [
      {
        name: "CountMinValue",
        description: "",
        expression: "state.count >= 0",
        location: { file: "test.ts", line: 1 },
      },
      {
        name: "CountMaxValue",
        description: "",
        expression: "state.count <= 100",
        location: { file: "test.ts", line: 2 },
      },
    ];

    const generator = new InvariantGenerator();
    const config = generator.generateConfigInvariants(invariants);

    expect(config).toHaveLength(2);
    expect(config[0]).toBe("INVARIANT CountMinValue");
    expect(config[1]).toBe("INVARIANT CountMaxValue");
  });

  test("generates multiple invariants", () => {
    const invariants = [
      {
        name: "Inv1",
        description: "First",
        expression: "state.a > 0",
        location: { file: "test.ts", line: 1 },
      },
      {
        name: "Inv2",
        description: "Second",
        expression: "state.b > 0",
        location: { file: "test.ts", line: 2 },
      },
      {
        name: "Inv3",
        description: "Third",
        expression: "state.c > 0",
        location: { file: "test.ts", line: 3 },
      },
    ];

    const generator = new InvariantGenerator();
    const tla = generator.generateTLAInvariants(invariants, mockTranslate);

    expect(tla).toHaveLength(3);
    expect(tla[0]).toContain("Inv1 ==");
    expect(tla[1]).toContain("Inv2 ==");
    expect(tla[2]).toContain("Inv3 ==");
  });
});
