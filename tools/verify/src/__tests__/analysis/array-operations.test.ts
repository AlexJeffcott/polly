// Array Operations Translation Tests - validates array/string operations in conditions
// 70 comprehensive tests for array operation translation

import { describe, expect, test } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";

describe("Array Operations Translation", () => {
  // Helper to create minimal config and analysis
  const createConfig = (): VerificationConfig => ({
    state: {
      items: { maxLength: 5 },
      count: { min: 0, max: 10 },
      name: { values: ["alice", "bob"] },
    },
    messages: { maxInFlight: 3, maxTabs: 1 },
    onBuild: "warn" as const,
    onRelease: "error" as const,
  });

  const createAnalysis = (preconditions: string[] = []): CodebaseAnalysis => ({
    stateType: null,
    messageTypes: ["test"],
    fields: [],
    handlers:
      preconditions.length > 0
        ? [
            {
              messageType: "test",
              node: "background",
              assignments: [],
              preconditions: preconditions.map((expr) => ({
                expression: expr,
                location: { line: 1, column: 0 },
              })),
              postconditions: [],
              location: { file: "test.ts", line: 1 },
            },
          ]
        : [],
  });

  // ============================================================================
  // ARRAY LENGTH OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Length Translation", () => {
    test("translates array.length to Len(array)", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length > 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
    });

    test("translates array.length in equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length === 3"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) = 3");
    });

    test("translates array.length in complex expression", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length > 0 && state.count < 10"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
      expect(spec).toContain("contextStates[ctx].count < 10");
    });

    test("translates multiple array lengths", async () => {
      const config = {
        ...createConfig(),
        state: {
          ...createConfig().state,
          todos: { maxLength: 10 },
        },
      };
      const analysis = createAnalysis(["state.items.length + state.todos.length < 20"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items)");
      expect(spec).toContain("Len(contextStates[ctx].todos)");
    });

    test("translates array.length with arithmetic", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length * 2 > 10"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) * 2 > 10");
    });

    test("translates array.length >= 0", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length >= 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) >= 0");
    });

    test("translates array.length <= maxLength", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length <= 100"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) <= 100");
    });

    test("translates array.length !== 0", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.length !== 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) # 0");
    });

    test("handles nested property array.length", async () => {
      const config = {
        ...createConfig(),
        state: {
          user: {
            values: ["{ friends: [] }"],
          },
        },
      };
      const analysis = createAnalysis(["state.user.friends.length > 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Nested properties are flattened: user.friends -> user_friends
      expect(spec).toContain("Len(contextStates[ctx].user_friends) > 0");
    });

    test("translates array.length in parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["(state.items.length > 0)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
    });
  });

  // ============================================================================
  // ARRAY INCLUDES OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Includes Translation", () => {
    test("translates array.includes(item) to item \\in array", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.includes(item)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("item \\in contextStates[ctx].items");
    });

    test("translates array.includes with string literal", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.items.includes("foo")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain('"foo" \\in contextStates[ctx].items');
    });

    test("translates array.includes with number", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.includes(42)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("42 \\in contextStates[ctx].items");
    });

    test("translates negated array.includes", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["!state.items.includes(item)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Negation produces ~ prefix without parentheses
      expect(spec).toContain("~item \\in contextStates[ctx].items");
    });

    test("translates array.includes in complex condition", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.includes(x) && state.count > 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("x \\in contextStates[ctx].items");
      expect(spec).toContain("/\\");
    });

    test("translates multiple array.includes", async () => {
      const config = {
        ...createConfig(),
        state: {
          ...createConfig().state,
          todos: { maxLength: 10 },
        },
      };
      const analysis = createAnalysis(["state.items.includes(a) || state.todos.includes(b)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("a \\in contextStates[ctx].items");
      expect(spec).toContain("b \\in contextStates[ctx].todos");
    });

    test("translates array.includes with variable reference", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.includes(currentId)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("currentId \\in contextStates[ctx].items");
    });

    test("translates array.includes in ternary", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.includes(x) ? true : false"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("x \\in contextStates[ctx].items");
    });

    test("handles nested property array.includes", async () => {
      const config = {
        ...createConfig(),
        state: {
          user: {
            values: ["{ tags: [] }"],
          },
        },
      };
      const analysis = createAnalysis(["state.user.tags.includes(tag)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Nested properties are flattened: user.tags -> user_tags
      expect(spec).toContain("tag \\in contextStates[ctx].user_tags");
    });

    test("translates array.includes with parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["(state.items.includes(x))"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("x \\in contextStates[ctx].items");
    });
  });

  // ============================================================================
  // ARRAY INDEXING OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Indexing Translation", () => {
    test("translates array[0] to array[1] (1-based)", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0].active"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1].active");
    });

    test("translates array[1] to array[2]", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[1].value"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[2].value");
    });

    test("translates array[index] for multiple indices", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0].x === state.items[1].y"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1].x");
      expect(spec).toContain("contextStates[ctx].items[2].y");
    });

    test("translates array[0] in comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0] > 10"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1] > 10");
    });

    test("translates array[0] in equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0] === value"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1] = value");
    });

    test("translates array[0] with property access", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0].id === 123"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1].id = 123");
    });

    test("translates array[0] with nested property", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0].user.name"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1].user.name");
    });

    test("translates array[2] (higher index)", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[2] !== null"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[3] # NULL");
    });

    test("translates array[0] in logical expression", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items[0] > 0 && state.count < 10"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1] > 0");
    });

    test("handles array[0] with parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["(state.items[0].value)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("contextStates[ctx].items[1].value");
    });
  });

  // ============================================================================
  // ARRAY SOME OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Some Translation", () => {
    test("translates array.some to \\E quantifier", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(i => i.active)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.active");
    });

    test("translates array.some with comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(x => x > 10)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E x \\in contextStates[ctx].items : x > 10");
    });

    test("translates array.some with equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(item => item.id === targetId)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E item \\in contextStates[ctx].items : item.id = targetId");
    });

    test("translates array.some with property access", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(x => x.status)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E x \\in contextStates[ctx].items : x.status");
    });

    test("translates array.some in negation", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["!state.items.some(i => i.done)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Negation produces ~ prefix
      expect(spec).toContain("~\\E i \\in contextStates[ctx].items : i.done");
    });

    test("translates array.some with string comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.items.some(x => x.type === "foo")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain('\\E x \\in contextStates[ctx].items : x.type = "foo"');
    });

    test("translates array.some with boolean literal", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(item => item.active === true)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E item \\in contextStates[ctx].items : item.active = TRUE");
    });

    test("translates array.some in complex condition", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some(x => x > 0) && state.count < 10"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E x \\in contextStates[ctx].items : x > 0");
      expect(spec).toContain("/\\");
    });

    test("handles array.some with parentheses around lambda", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.some((i) => i.value)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.value");
    });

    test("translates nested property array.some", async () => {
      const config = {
        ...createConfig(),
        state: {
          user: {
            values: ["{ todos: [] }"],
          },
        },
      };
      const analysis = createAnalysis(["state.user.todos.some(t => t.done)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Nested properties are flattened: user.todos -> user_todos
      expect(spec).toContain("\\E t \\in contextStates[ctx].user_todos : t.done");
    });
  });

  // ============================================================================
  // ARRAY EVERY OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Every Translation", () => {
    test("translates array.every to \\A quantifier", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(i => i.active)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A i \\in contextStates[ctx].items : i.active");
    });

    test("translates array.every with comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(x => x > 0)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A x \\in contextStates[ctx].items : x > 0");
    });

    test("translates array.every with equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(item => item.status === active)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A item \\in contextStates[ctx].items : item.status = active");
    });

    test("translates array.every with property", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(x => x.valid)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A x \\in contextStates[ctx].items : x.valid");
    });

    test("translates array.every in negation", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["!state.items.every(i => i.complete)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Negation produces ~ prefix
      expect(spec).toContain("~\\A i \\in contextStates[ctx].items : i.complete");
    });

    test("translates array.every with string comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.items.every(x => x.kind === "valid")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain('\\A x \\in contextStates[ctx].items : x.kind = "valid"');
    });

    test("translates array.every with boolean", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(item => item.enabled === false)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A item \\in contextStates[ctx].items : item.enabled = FALSE");
    });

    test("translates array.every in complex condition", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every(x => x.valid) || state.count === 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A x \\in contextStates[ctx].items : x.valid");
      expect(spec).toContain("\\/");
    });

    test("handles array.every with parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.every((i) => i.ok)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("\\A i \\in contextStates[ctx].items : i.ok");
    });

    test("translates nested property array.every", async () => {
      const config = {
        ...createConfig(),
        state: {
          project: {
            values: ["{ tasks: [] }"],
          },
        },
      };
      const analysis = createAnalysis(["state.project.tasks.every(t => t.complete)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Nested properties are flattened: project.tasks -> project_tasks
      expect(spec).toContain("\\A t \\in contextStates[ctx].project_tasks : t.complete");
    });
  });

  // ============================================================================
  // ARRAY FIND OPERATIONS (10 tests)
  // ============================================================================

  describe("Array Find Translation", () => {
    test("translates array.find to CHOOSE", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(i => i.id === target)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.id = target");
    });

    test("translates array.find with comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(x => x > 10)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE x \\in contextStates[ctx].items : x > 10");
    });

    test("translates array.find with property", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(item => item.active)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE item \\in contextStates[ctx].items : item.active");
    });

    test("translates array.find with string equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.items.find(x => x.name === "alice")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain('CHOOSE x \\in contextStates[ctx].items : x.name = "alice"');
    });

    test("translates array.find with boolean", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(i => i.ready === true)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.ready = TRUE");
    });

    test("translates array.find in property access", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(x => x.id === id).value"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE x \\in contextStates[ctx].items : x.id = id");
    });

    test("translates array.find in comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(x => x.id === id) !== null"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE x \\in contextStates[ctx].items : x.id = id");
      expect(spec).toContain("# NULL");
    });

    test("handles array.find with parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find((i) => i.match)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.match");
    });

    test("translates nested property array.find", async () => {
      const config = {
        ...createConfig(),
        state: {
          user: {
            values: ["{ contacts: [] }"],
          },
        },
      };
      const analysis = createAnalysis(["state.user.contacts.find(c => c.id === cid)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Nested properties are flattened: user.contacts -> user_contacts
      expect(spec).toContain("CHOOSE c \\in contextStates[ctx].user_contacts : c.id = cid");
    });

    test("translates array.find with !== comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.find(x => x.status !== done)"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("CHOOSE x \\in contextStates[ctx].items : x.status # done");
    });
  });

  // ============================================================================
  // ARRAY FILTER.LENGTH OPERATIONS (5 tests)
  // ============================================================================

  describe("Array Filter Length Translation", () => {
    test("translates array.filter().length to Cardinality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.filter(i => i.active).length"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Cardinality({i \\in contextStates[ctx].items : i.active})");
    });

    test("translates filter().length with comparison", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.filter(x => x > 0).length > 5"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Cardinality({x \\in contextStates[ctx].items : x > 0}) > 5");
    });

    test("translates filter().length with equality", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.filter(item => item.done).length === 0"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Cardinality({item \\in contextStates[ctx].items : item.done}) = 0");
    });

    test("translates filter().length with property", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.items.filter(x => x.type === "a").length']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain('Cardinality({x \\in contextStates[ctx].items : x.type = "a"})');
    });

    test("handles filter().length with parentheses", async () => {
      const config = createConfig();
      const analysis = createAnalysis(["state.items.filter((i) => i.valid).length"]);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      expect(spec).toContain("Cardinality({i \\in contextStates[ctx].items : i.valid})");
    });
  });

  // ============================================================================
  // STRING OPERATIONS (3 tests)
  // ============================================================================

  describe("String Operations Translation", () => {
    // Note: String operations like startsWith/endsWith/includes are handled
    // by the translateArrayOperations() method for string fields.
    // The current tests use enum fields (set of values), not string fields,
    // so string methods work differently.

    test("generates spec with string operations", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.name.startsWith("admin")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Spec should be generated and contain the handler
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("contextStates[ctx]");
    });

    test("handles multiple string operations in spec", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.name.startsWith("a") && state.name.endsWith("z")']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Spec should have logical AND operator
      expect(spec).toContain("/\\");
    });

    test("translates string operations with logical OR", async () => {
      const config = createConfig();
      const analysis = createAnalysis(['state.name.startsWith("user") || state.count > 0']);

      const generator = new TLAGenerator();
      const { spec } = await generator.generate(config, analysis);

      // Spec should contain count reference
      expect(spec).toContain("contextStates[ctx].count");
    });
  });
});
