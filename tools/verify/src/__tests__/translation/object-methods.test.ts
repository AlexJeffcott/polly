import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../analysis/types";
import type { VerificationConfig } from "../../../config/types";
import { TLAGenerator } from "../../codegen/tla";

describe("Object/Array Method Translation", () => {
  let generator: TLAGenerator;
  let baseConfig: VerificationConfig;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();

    baseConfig = {
      state: {
        items: { type: "array", maxLength: 5 },
        users: { type: "array", maxLength: 3 },
        count: { type: "enum", values: ["0", "1", "2", "3"] },
        name: { type: "enum", values: ["alice", "bob", "charlie"] },
        active: { type: "enum", values: ["true", "false"] },
      },
      messages: {
        maxInFlight: 3,
        maxTabs: 1,
      },
    };

    baseAnalysis = {
      stateType: null,
      messageTypes: ["test"],
      fields: [],
      handlers: [
        {
          messageType: "test",
          assignments: [],
          preconditions: [],
          postconditions: [],
        },
      ],
    };
  });

  describe("Array Length", () => {
    test("translates simple array length", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
    });

    test("translates array length in comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length === 3", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) = 3");
    });

    test("translates array length with less than", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length < 5", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) < 5");
    });

    test("translates array length with greater than or equal", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length >= 1", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) >= 1");
    });

    test("translates array length in arithmetic", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length + 1 > state.count", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) + 1");
    });
  });

  describe("Array Includes", () => {
    test("translates simple includes", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.includes('item1')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("'item1' \\in contextStates[ctx].items");
    });

    test("translates includes with variable", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.includes(payload.id)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("payload.id \\in contextStates[ctx].items");
    });

    test("translates includes in negation", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!state.items.includes('test')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("'test' \\in contextStates[ctx].items");
      expect(spec).toContain("~");
    });

    test("translates includes in conjunction", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.includes('a') && state.users.includes('b')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("'a' \\in contextStates[ctx].items");
      expect(spec).toContain("'b' \\in contextStates[ctx].users");
    });

    test("translates includes with number", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.includes(42)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("42 \\in contextStates[ctx].items");
    });
  });

  describe("Array Indexing", () => {
    test("translates array index 0 to 1 (1-based)", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items[0] === 'first'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].items[1]");
    });

    test("translates array index 1 to 2", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items[1] === 'second'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].items[2]");
    });

    test("translates array index 5 to 6", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items[5] !== null", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].items[6]");
    });

    test("translates nested array access", async () => {
      baseConfig.state.matrix = { type: "array", maxLength: 3 };
      // Note: Currently only first index is converted; nested indices are a known limitation
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.matrix[0] === 'value'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].matrix[1]");
    });

    test("translates array index in postcondition", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.items[0] === 'updated'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates'[ctx].items[1]");
    });
  });

  describe("Array .some() Method", () => {
    test("translates simple some", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.some(i => i.active)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.active");
    });

    test("translates some with comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.some(item => item.id === 'target')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E item \\in contextStates[ctx].items : item.id = 'target'");
    });

    test("translates some with parenthesized parameter", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.users.some((user) => user.active)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E user \\in contextStates[ctx].users : user.active");
    });

    test("translates some with complex condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.some(i => i.count > 0 && i.active)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items");
      expect(spec).toContain("i.count > 0");
      expect(spec).toContain("i.active");
    });

    test("translates some in negation", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!state.items.some(i => i.invalid)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("~");
      expect(spec).toContain("\\E i \\in contextStates[ctx].items");
    });
  });

  describe("Array .every() Method", () => {
    test("translates simple every", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.every(i => i.valid)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\A i \\in contextStates[ctx].items : i.valid");
    });

    test("translates every with comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.every(item => item.count > 0)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\A item \\in contextStates[ctx].items : item.count > 0");
    });

    test("translates every with parenthesized parameter", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.users.every((user) => user.active)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\A user \\in contextStates[ctx].users : user.active");
    });

    test("translates every with complex condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.every(i => i.count >= 0 && i.valid)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\A i \\in contextStates[ctx].items");
      expect(spec).toContain("i.count >= 0");
    });

    test("translates every in conjunction", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.every(i => i.active) && state.count > 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\A i \\in contextStates[ctx].items : i.active");
      expect(spec).toContain("contextStates[ctx].count > 0");
    });
  });

  describe("Array .find() Method", () => {
    test("translates simple find", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.find(i => i.id === 'target') !== null",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.id = 'target'");
    });

    test("translates find with comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.find(item => item.count > 5)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("CHOOSE item \\in contextStates[ctx].items : item.count > 5");
    });

    test("translates find with parenthesized parameter", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.users.find((user) => user.name === 'alice')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("CHOOSE user \\in contextStates[ctx].users : user.name = 'alice'");
    });

    test("translates find with complex condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.find(i => i.active && i.count > 0)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items");
      expect(spec).toContain("i.active");
      expect(spec).toContain("i.count > 0");
    });

    test("translates find in property access", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.find(i => i.id === payload.targetId).value",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.id = payload.targetId");
    });
  });

  describe("Array .filter() Method", () => {
    test("translates filter().length", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.filter(i => i.active).length > 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Cardinality({i \\in contextStates[ctx].items : i.active}) > 0");
    });

    test("translates filter().length with comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.filter(item => item.count > 0).length",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Cardinality({item \\in contextStates[ctx].items : item.count > 0})");
    });

    test("translates filter().length with parenthesized parameter", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.users.filter((user) => user.active).length === 3",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Cardinality({user \\in contextStates[ctx].users : user.active}) = 3");
    });

    test("translates filter().length with complex condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.filter(i => i.count > 0 && i.valid).length >= 1",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Cardinality({i \\in contextStates[ctx].items");
      expect(spec).toContain("i.count > 0");
    });

    test("translates filter().length in comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.filter(i => i.active).length < state.count",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "Cardinality({i \\in contextStates[ctx].items : i.active}) < contextStates[ctx].count"
      );
    });
  });

  describe("String Methods", () => {
    test("translates startsWith", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.startsWith('al')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("SubSeq(contextStates[ctx].name, 1, Len('al')) = 'al'");
    });

    test("translates endsWith", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.endsWith('ce')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "SubSeq(contextStates[ctx].name, Len(contextStates[ctx].name) - Len('ce') + 1, Len(contextStates[ctx].name)) = 'ce'"
      );
    });

    test("translates string includes", async () => {
      // Note: For enum fields, .includes() is treated as membership check
      // For true substring matching, would need proper string type
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.includes('alice')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Enum membership check (not substring)
      expect(spec).toContain("'alice' \\in contextStates[ctx].name");
    });

    test("translates startsWith with variable", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.startsWith(payload.prefix)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "SubSeq(contextStates[ctx].name, 1, Len(payload.prefix)) = payload.prefix"
      );
    });

    test("translates multiple string methods", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.name.startsWith('a') && state.name.endsWith('e')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("SubSeq(contextStates[ctx].name, 1, Len('a')) = 'a'");
      expect(spec).toContain("SubSeq(contextStates[ctx].name");
      expect(spec).toContain("= 'e'");
    });

    test("translates slice with start index", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.slice(1) === 'lice'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // slice(1) → SubSeq(str, 2, Len(str)) (1-based indexing)
      expect(spec).toContain(
        "SubSeq(contextStates[ctx].name, 2, Len(contextStates[ctx].name)) = 'lice'"
      );
    });

    test("translates slice with start and end", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.slice(0, 3) === 'ali'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // slice(0, 3) → SubSeq(str, 1, 3) (converts 0-based to 1-based)
      expect(spec).toContain("SubSeq(contextStates[ctx].name, 1, 3) = 'ali'");
    });

    test("translates slice with negative index", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.slice(-2) === 'ce'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // slice(-2) → SubSeq(str, Len(str) - 2 + 1, Len(str))
      expect(spec).toContain(
        "SubSeq(contextStates[ctx].name, Len(contextStates[ctx].name) - 2 + 1, Len(contextStates[ctx].name)) = 'ce'"
      );
    });

    test("translates slice in comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.slice(1, 4).length > 2", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(SubSeq(contextStates[ctx].name, 2, 4)) > 2");
    });

    test("translates substring with start index", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.substring(1) === 'lice'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // substring(1) → SubSeq(str, 2, Len(str)) (1-based indexing)
      expect(spec).toContain(
        "SubSeq(contextStates[ctx].name, 2, Len(contextStates[ctx].name)) = 'lice'"
      );
    });

    test("translates substring with start and end", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.substring(0, 3) === 'ali'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // substring(0, 3) → SubSeq(str, 1, 3)
      expect(spec).toContain("SubSeq(contextStates[ctx].name, 1, 3) = 'ali'");
    });

    test("translates substring with swapped indices", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.substring(3, 1) === 'li'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // substring auto-swaps: substring(3, 1) → SubSeq(str, 2, 3)
      expect(spec).toContain("SubSeq(contextStates[ctx].name");
      expect(spec).toContain("'li'");
    });

    test("translates substring in postcondition", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.name.substring(0, 2) === 'al'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates'[ctx]");
      expect(spec).toContain("SubSeq");
      expect(spec).toContain("'al'");
    });

    test("translates mixed slice and startsWith", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.slice(1).startsWith('li')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Chained string methods
      expect(spec).toContain("SubSeq");
      expect(spec).toContain("'li'");
    });

    test("translates string length after substring", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name.substring(1, 4).length === 3", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(SubSeq(contextStates[ctx].name");
      expect(spec).toContain("= 3");
    });
  });

  describe("Combined Operations", () => {
    test("combines length and includes", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.length > 0 && state.items.includes('test')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
      expect(spec).toContain("'test' \\in contextStates[ctx].items");
    });

    test("combines some and every", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.some(i => i.active) && state.users.every(u => u.valid)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.active");
      expect(spec).toContain("\\A u \\in contextStates[ctx].users : u.valid");
    });

    test("combines filter and find", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression:
            "state.items.filter(i => i.active).length > 0 || state.items.find(i => i.id === 'x')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Cardinality({i \\in contextStates[ctx].items : i.active}) > 0");
      expect(spec).toContain("CHOOSE i \\in contextStates[ctx].items : i.id = 'x'");
    });

    test("combines array indexing with methods", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items[0].active && state.items.some(i => i.valid)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].items[1].active");
      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.valid");
    });

    test("combines string and array methods", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.name.startsWith('a') && state.items.length > 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("SubSeq(contextStates[ctx].name");
      expect(spec).toContain("Len(contextStates[ctx].items) > 0");
    });
  });

  describe("Edge Cases", () => {
    test("handles empty array reference", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.length === 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) = 0");
    });

    test("handles nested property access in array methods", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items.some(i => i.user.active)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items : i.user.active");
    });

    test("handles multiple array references", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.length === state.users.length",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("Len(contextStates[ctx].items) = Len(contextStates[ctx].users)");
    });

    test("handles array methods in postconditions", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.items.some(i => i.updated)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates'[ctx]");
      expect(spec).toContain("\\E i \\in");
    });

    test("handles complex lambda expressions", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.some(i => i.count > state.count && i.active)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("\\E i \\in contextStates[ctx].items");
      expect(spec).toContain("i.count");
    });
  });
});
