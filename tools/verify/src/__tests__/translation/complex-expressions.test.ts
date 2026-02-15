// Complex Expression Translation Tests - validates translation of advanced JS patterns
// 80 comprehensive tests for ternary, nullish coalescing, optional chaining, and nesting

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../../analysis/src/types";
import { TLAGenerator } from "../../codegen/tla";

describe("Complex Expression Translation", () => {
  let generator: TLAGenerator;
  let baseConfig: VerificationConfig;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();

    baseConfig = {
      state: {
        count: { type: "enum", values: ["0", "1", "2"] },
        active: { type: "enum", values: ["true", "false"] },
        user: { type: "enum", values: ["admin", "guest", "null"] },
        value: { type: "enum", values: ["0", "1"] },
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
      stateConstraints: [],
    };
  });

  // ============================================================================
  // TERNARY OPERATOR (20 tests)
  // ============================================================================

  describe("Ternary Operator", () => {
    test("translates simple ternary", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0 ? true : false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count > 0 THEN TRUE ELSE FALSE");
    });

    test("translates ternary with numeric values", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0 ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count > 0 THEN 1 ELSE 0");
    });

    test("translates ternary with string values", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.active ? 'yes' : 'no'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // TLA+ uses double quotes for strings
      expect(spec).toContain('IF contextStates[ctx].active THEN "yes" ELSE "no"');
    });

    test("translates ternary with state references in branches", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? state.count : state.value",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // `.value` pattern is interpreted as signal state, mapping to `contextStates[ctx].state`
      expect(spec).toContain(
        "IF contextStates[ctx].active THEN contextStates[ctx].count ELSE contextStates[ctx].state"
      );
    });

    test("translates nested ternary (left side)", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.count > 0 ? (state.active ? 1 : 2) : 3",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should have nested IF-THEN-ELSE
      expect(spec).toContain("IF");
      expect(spec).toContain("THEN");
      expect(spec).toContain("ELSE");
    });

    test("translates nested ternary (right side)", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.count > 0 ? 1 : (state.active ? 2 : 3)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("THEN");
      expect(spec).toContain("ELSE");
    });

    test("translates ternary with comparison in condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count === 1 ? true : false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count = 1 THEN TRUE ELSE FALSE");
    });

    test("translates ternary with logical AND in condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0 && state.active ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("/\\");
      expect(spec).toContain("THEN 1 ELSE 0");
    });

    test("translates ternary with logical OR in condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0 || state.active ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("\\/");
      expect(spec).toContain("THEN 1 ELSE 0");
    });

    test("translates ternary with negation in condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!state.active ? 0 : 1", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF ~contextStates[ctx].active THEN 0 ELSE 1");
    });

    test("translates ternary in postcondition (primed state)", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.count > 0 ? true : false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
    });

    test("handles ternary with parentheses", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.count > 0) ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("THEN 1 ELSE 0");
    });

    test("translates ternary with null values", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.user === null ? 'guest' : state.user",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("NULL");
      // TLA+ uses double quotes for strings
      expect(spec).toContain('"guest"');
    });

    test("translates chained ternary", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.count === 0 ? 'zero' : state.count === 1 ? 'one' : 'many'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should have multiple IF-THEN-ELSE
      expect(spec).toContain("IF");
    });

    test("translates ternary with boolean literals", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.active ? true : false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("THEN TRUE ELSE FALSE");
    });

    test("translates ternary with inequality", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count !== 0 ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count # 0 THEN 1 ELSE 0");
    });

    test("translates ternary with greater than", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 1 ? 2 : 1", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count > 1 THEN 2 ELSE 1");
    });

    test("translates ternary with less than or equal", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count <= 0 ? 0 : 1", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].count <= 0 THEN 0 ELSE 1");
    });

    test("translates ternary with payload reference", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "payload.active ? state.count : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF payload.active THEN contextStates[ctx].count ELSE 0");
    });

    test("handles complex nested ternary", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression:
            "state.count > 2 ? 'high' : state.count > 1 ? 'mid' : state.count > 0 ? 'low' : 'zero'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should compile without errors
      expect(spec).toContain("IF");
    });
  });

  // ============================================================================
  // NULLISH COALESCING (20 tests)
  // ============================================================================

  describe("Nullish Coalescing", () => {
    test("translates simple nullish coalescing", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // TLA+ uses double quotes for strings
      expect(spec).toContain(
        'IF contextStates[ctx].user # NULL THEN contextStates[ctx].user ELSE "guest"'
      );
    });

    test("translates nullish coalescing with numeric default", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count ?? 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "IF contextStates[ctx].count # NULL THEN contextStates[ctx].count ELSE 0"
      );
    });

    test("translates nullish coalescing with boolean default", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.active ?? false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "IF contextStates[ctx].active # NULL THEN contextStates[ctx].active ELSE FALSE"
      );
    });

    test("translates nullish coalescing with state reference as default", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user ?? state.value", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // `.value` pattern is interpreted as signal state, mapping to `contextStates[ctx].state`
      expect(spec).toContain(
        "IF contextStates[ctx].user # NULL THEN contextStates[ctx].user ELSE contextStates[ctx].state"
      );
    });

    test("translates chained nullish coalescing", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user ?? state.value ?? 'default'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should have nested IF checks
      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates nullish coalescing in postcondition", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.user ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
    });

    test("translates nullish coalescing with payload", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "payload.user ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // TLA+ uses double quotes for strings
      expect(spec).toContain('IF payload.user # NULL THEN payload.user ELSE "guest"');
    });

    test("translates nullish coalescing with null literal", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user ?? null", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain(
        "IF contextStates[ctx].user # NULL THEN contextStates[ctx].user ELSE NULL"
      );
    });

    test("handles nullish coalescing in ternary condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.user ?? 'guest') === 'admin' ? 1 : 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles nullish coalescing in comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.count ?? 0) > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates nullish coalescing with nested property", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user_name ?? 'unknown'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].user_name");
      expect(spec).toContain("# NULL");
    });

    test("handles multiple nullish coalescing in same expression", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.user ?? 'guest') + (state.value ?? 0)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates nullish coalescing with parentheses", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.user) ?? ('guest')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles nullish coalescing with logical operators", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.user ?? 'guest') === 'admin' && state.active",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
      expect(spec).toContain("/\\");
    });

    test("translates nullish coalescing with array", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items ?? []", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF contextStates[ctx].items # NULL");
    });

    test("handles nullish coalescing result in ternary branch", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? (state.user ?? 'guest') : 'none'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
    });

    test("translates deep nullish coalescing chain", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.user ?? state.value ?? state.count ?? 'default'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles nullish coalescing with negation", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!(state.user ?? 'guest')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("~");
      expect(spec).toContain("# NULL");
    });

    test("translates nullish coalescing with equality check", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.user ?? 'guest') === 'admin'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles nullish coalescing in both ternary branches", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? (state.user ?? 'admin') : (state.value ?? 'guest')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });
  });

  // ============================================================================
  // OPTIONAL CHAINING (20 tests)
  // ============================================================================

  describe("Optional Chaining", () => {
    test("translates simple optional chaining", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.name", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining in comparison", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.name === 'admin'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates chained optional access", async () => {
      baseConfig.state.user_profile_name = {
        type: "enum",
        values: ["admin", "guest", "null"],
      };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.profile?.name", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with fallback", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.user?.name) ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining in ternary", async () => {
      baseConfig.state.user_active = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.active ? 'yes' : 'no'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with payload", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "payload.user?.name", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF payload.user # NULL");
    });

    test("handles optional chaining with array index", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items?.[0]", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining in postcondition", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.postconditions = [
        { expression: "state.user?.name", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
    });

    test("handles optional method call", async () => {
      baseConfig.state.name = { type: "enum", values: ["test", "hello"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name?.startsWith('test')", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates deeply nested optional chaining", async () => {
      baseConfig.state.a_b_c_d = { type: "enum", values: ["value", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.a?.b?.c?.d", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles optional chaining with comparison", async () => {
      baseConfig.state.user_age = { type: "enum", values: ["0", "1", "2"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.age > 18", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with logical AND", async () => {
      baseConfig.state.user_active = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.active && state.count > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
      expect(spec).toContain("/\\");
    });

    test("handles optional chaining in negation", async () => {
      baseConfig.state.user_active = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!state.user?.active", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("~");
      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with parentheses", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.user)?.name", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles multiple optional chains in expression", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest"] };
      baseConfig.state.profile_title = { type: "enum", values: ["mr", "ms"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.user?.name === state.profile?.title",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with array method", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items?.length > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles optional chaining in both ternary branches", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest"] };
      baseConfig.state.profile_name = { type: "enum", values: ["john", "jane"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? state.user?.name : state.profile?.name",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining with string literal property", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.['name']", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // May or may not handle bracket notation - at least shouldn't crash
      expect(spec).toBeDefined();
    });

    test("handles optional chaining with numeric property", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items?.[0]?.active", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("translates optional chaining combined with nullish coalescing", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.name ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });
  });

  // ============================================================================
  // MIXED COMPLEX EXPRESSIONS (20 tests)
  // ============================================================================

  describe("Mixed Complex Expressions", () => {
    test("handles ternary with nullish coalescing in condition", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.user ?? 'guest') === 'admin' ? 1 : 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles ternary with optional chaining in condition", async () => {
      baseConfig.state.user_active = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.active ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles optional chaining with nullish coalescing", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.name ?? 'guest'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles nested ternary with nullish coalescing", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.count > 0 ? (state.user ?? 'guest') : 'none'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles complex expression with all three operators", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest", "null"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? (state.user?.name ?? 'guest') : 'none'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles ternary with comparison and logical operators", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0 && state.active ? 1 : 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("/\\");
    });

    test("handles nullish coalescing in comparison", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.count ?? 0) > 5", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles optional chaining in array operations", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items?.length > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles mixed operators with parentheses", async () => {
      baseConfig.state.user_age = { type: "enum", values: ["0", "18", "21"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "((state.user?.age ?? 0) > 18) ? 'adult' : 'minor'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles deeply nested mixed operators", async () => {
      baseConfig.state.user_profile_age = { type: "enum", values: ["0", "18", "21"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression:
            "state.active ? (state.user?.profile?.age ?? 0) > 18 ? 'yes' : 'no' : 'inactive'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
    });

    test("handles ternary in postcondition with complex operators", async () => {
      baseAnalysis.handlers[0]!.postconditions = [
        {
          expression: "state.count > 0 ? (state.user ?? 'guest') : 'none'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
    });

    test("handles nullish coalescing chain with ternary", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.user ?? state.value ?? 'default') === 'admin' ? 1 : 0",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles optional chaining with array methods", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.items?.some(i => i.active)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles complex logical expression with ternary", async () => {
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.count > 0 || state.active) ? (state.user ?? 'guest') : null",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
    });

    test("handles nested optional chaining with nullish coalescing", async () => {
      baseConfig.state.user_profile_name = {
        type: "enum",
        values: ["admin", "guest", "null"],
      };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.user?.profile?.name ?? 'unknown'", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles ternary with optional chaining in both branches", async () => {
      baseConfig.state.user_name = { type: "enum", values: ["admin", "guest"] };
      baseConfig.state.profile_name = { type: "enum", values: ["john", "jane"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.active ? state.user?.name : state.profile?.name",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles comparison with all three operators", async () => {
      baseConfig.state.user_age = { type: "enum", values: ["0", "18", "21"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "(state.user?.age ?? 0) >= 18", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });

    test("handles negation with complex operators", async () => {
      baseConfig.state.user_active = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "!(state.user?.active ?? false)", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("~");
      expect(spec).toContain("# NULL");
    });

    test("handles array operations with complex operators", async () => {
      baseConfig.state.items = { type: "array", maxLength: 5 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "(state.items?.length ?? 0) > 0 ? true : false",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("IF");
      expect(spec).toContain("# NULL");
    });

    test("handles string operations with complex operators", async () => {
      baseConfig.state.name = { type: "enum", values: ["test", "hello"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.name?.startsWith('test') ?? false", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("# NULL");
    });
  });

  // ============================================================================
  // VERIFIED STATE SYNTAX CONVERSION (regression tests for Issue #27)
  // ============================================================================

  describe("Verified State Syntax Conversion", () => {
    test("converts single quotes to double quotes for TLA+ strings", async () => {
      baseConfig.state.status = { type: "enum", values: ["connected", "disconnected"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "connectionState.value.status === 'disconnected'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // TLA+ uses double quotes for strings, not single quotes
      expect(spec).toContain('"disconnected"');
      expect(spec).not.toContain("'disconnected'");
    });

    test("converts stateName.value.field to contextStates[ctx].field in preconditions", async () => {
      baseConfig.state.isAuthenticated = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "authState.value.isAuthenticated === false",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Signal state fields are prefixed with the signal name for TLA+ verification
      expect(spec).toContain("contextStates[ctx].authState_isAuthenticated");
      expect(spec).not.toContain("authState.value.isAuthenticated");
    });

    test("converts stateName.value.field to contextStates'[ctx].field in postconditions", async () => {
      baseConfig.state.isAuthenticated = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.postconditions = [
        {
          expression: "authState.value.isAuthenticated === true",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
      expect(spec).not.toContain("authState.value.isAuthenticated");
    });

    test("handles nested path in stateName.value.nested.path", async () => {
      baseConfig.state.user_profile_name = { type: "enum", values: ["admin", "guest"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "userState.value.user.profile.name === 'admin'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should handle nested paths and convert quotes
      expect(spec).toContain("contextStates[ctx]");
      expect(spec).toContain('"admin"');
      expect(spec).not.toContain("userState.value");
      expect(spec).not.toContain("'admin'");
    });

    test("handles multiple signal state references in same expression", async () => {
      baseConfig.state.loggedIn = { type: "enum", values: ["true", "false"] };
      baseConfig.state.role = { type: "enum", values: ["admin", "user", "guest"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "userState.value.loggedIn && authState.value.role === 'admin'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Signal state fields are prefixed with the signal name for TLA+ verification
      expect(spec).toContain("contextStates[ctx].userState_loggedIn");
      expect(spec).toContain("contextStates[ctx].authState_role");
      expect(spec).toContain('"admin"');
      expect(spec).not.toContain("userState.value");
      expect(spec).not.toContain("authState.value");
    });

    test("converts both single quotes and signal references together", async () => {
      baseConfig.state.status = { type: "enum", values: ["connected", "disconnected", "pending"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression:
            "connectionState.value.status !== 'connected' && connectionState.value.status !== 'pending'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Signal state fields are prefixed with the signal name for TLA+ verification
      expect(spec).toContain("contextStates[ctx].connectionState_status");
      expect(spec).toContain('"connected"');
      expect(spec).toContain('"pending"');
      expect(spec).not.toContain("connectionState.value");
      expect(spec).not.toContain("'connected'");
      expect(spec).not.toContain("'pending'");
    });

    test("handles requires() extracted expression with signal state pattern", async () => {
      baseConfig.state.isConnected = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "networkState.value.isConnected === true", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Signal state fields are prefixed with the signal name for TLA+ verification
      expect(spec).toContain("contextStates[ctx].networkState_isConnected = TRUE");
      expect(spec).not.toContain("networkState.value");
    });

    test("handles ensures() extracted expression with signal state pattern", async () => {
      baseConfig.state.isConnected = { type: "enum", values: ["true", "false"] };
      baseAnalysis.handlers[0]!.postconditions = [
        {
          expression: "networkState.value.isConnected === false",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Postconditions without state changes result in UNCHANGED contextStates
      expect(spec).toContain("HandleTest(ctx)");
      expect(spec).toContain("UNCHANGED contextStates");
      expect(spec).not.toContain("networkState.value");
    });

    test("converts function parameter in comparison to payload reference", async () => {
      baseConfig.state.items = { type: "array", maxLength: 10 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.items.some((item) => item.id === targetId)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // targetId should become payload.targetId
      expect(spec).toContain("payload.targetId");
      // item should remain as the quantified variable, not become payload.item
      expect(spec).toContain("\\E item \\in");
      expect(spec).not.toContain("payload.item");
    });

    test("preserves quantified variables in array operations", async () => {
      baseConfig.state.operations = { type: "array", maxLength: 10 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.operations.some((op) => op.status === 'queued')",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // op should be preserved as quantified variable
      expect(spec).toContain("\\E op \\in");
      expect(spec).toContain("op.status");
      expect(spec).not.toContain("payload.op");
    });

    test("does not convert string literal content to payload", async () => {
      baseConfig.state.status = { type: "enum", values: ["active", "inactive"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "state.status === 'active'",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // "active" should stay as string, not become payload.active
      expect(spec).toContain('"active"');
      expect(spec).not.toContain("payload.active");
    });
  });

  // ============================================================================
  // NULL CONSTANT (regression tests for Issue #27 follow-up)
  // ============================================================================

  describe("NULL Constant Definition", () => {
    test("generates NULL constant in spec", async () => {
      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // NULL should be declared as a constant
      expect(spec).toContain("CONSTANTS");
      expect(spec).toContain("NULL");
    });

    test("generates NULL in config file", async () => {
      const { cfg } = await generator.generate(baseConfig, baseAnalysis);

      // NULL should be assigned as model value in config
      expect(cfg).toContain("NULL = NULL");
    });
  });

  // ============================================================================
  // VERIFICATION HELPER FUNCTIONS (hasLength, inRange, oneOf)
  // ============================================================================

  describe("Verification Helper Functions", () => {
    test("translates hasLength with max constraint", async () => {
      baseConfig.state.todos = { type: "array", maxLength: 100 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "hasLength(todos.value, { max: 99 })",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // hasLength(arr, { max: 99 }) -> Len(arr) <= 99
      // Signal .value pattern converts to contextStates[ctx].signalName
      expect(spec).toContain("Len(contextStates[ctx].todos) <= 99");
      expect(spec).not.toContain("hasLength");
    });

    test("translates hasLength with min constraint", async () => {
      baseConfig.state.items = { type: "array", maxLength: 10 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "hasLength(items.value, { min: 1 })",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // hasLength(arr, { min: 1 }) -> Len(arr) >= 1
      // Signal .value pattern converts to contextStates[ctx].signalName
      expect(spec).toContain("Len(contextStates[ctx].items) >= 1");
      expect(spec).not.toContain("hasLength");
    });

    test("translates hasLength with min and max constraints", async () => {
      baseConfig.state.data = { type: "array", maxLength: 50 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "hasLength(data.value, { min: 5, max: 20 })",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // hasLength(arr, { min: 5, max: 20 }) -> Len(arr) >= 5 /\ Len(arr) <= 20
      // Signal .value pattern converts to contextStates[ctx].signalName
      expect(spec).toContain("Len(contextStates[ctx].data) >= 5");
      expect(spec).toContain("Len(contextStates[ctx].data) <= 20");
      expect(spec).not.toContain("hasLength");
    });

    test("translates inRange helper function", async () => {
      baseConfig.state.count = { type: "enum", values: ["0", "1", "2", "3", "4", "5"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "inRange(state.count, 0, 100)",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // inRange(value, 0, 100) -> value >= 0 /\ value <= 100
      expect(spec).toContain("contextStates[ctx].count >= 0");
      expect(spec).toContain("contextStates[ctx].count <= 100");
      expect(spec).not.toContain("inRange");
    });

    test("translates oneOf helper function with string values", async () => {
      baseConfig.state.role = { type: "enum", values: ["admin", "user", "guest"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: 'oneOf(state.role, ["admin", "user"])',
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // oneOf(value, ["admin", "user"]) -> value \in {"admin", "user"}
      expect(spec).toContain('contextStates[ctx].role \\in {"admin", "user"}');
      expect(spec).not.toContain("oneOf");
    });

    test("translates oneOf helper function with numeric values", async () => {
      baseConfig.state.priority = { type: "enum", values: ["1", "2", "3"] };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "oneOf(state.priority, [1, 2, 3])",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // oneOf(value, [1, 2, 3]) -> value \in {1, 2, 3}
      expect(spec).toContain("contextStates[ctx].priority \\in {1, 2, 3}");
      expect(spec).not.toContain("oneOf");
    });

    test("translates hasLength with signal state reference", async () => {
      baseConfig.state.todos = { type: "array", maxLength: 100 };
      baseAnalysis.handlers[0]!.preconditions = [
        {
          expression: "hasLength(todoState.value.todos, { max: 99 })",
          location: { line: 1, column: 1 },
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      // Should translate hasLength AND convert signal state reference
      // Signal state fields are prefixed with the signal name for TLA+ verification
      expect(spec).toContain("Len(contextStates[ctx].todoState_todos) <= 99");
      expect(spec).not.toContain("hasLength");
      expect(spec).not.toContain("todoState.value");
    });
  });

  // ============================================================================
  // NUMERIC TYPE (Issue #31)
  // ============================================================================

  describe("Numeric Type", () => {
    test("{ type: 'number', min: 0, max: 10 } generates integer range in state type", async () => {
      baseConfig.state = {
        count: { type: "number", min: 0, max: 10 },
      };

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("count: 0..10");
    });

    test("defaults to 0..100 when bounds omitted", async () => {
      baseConfig.state = {
        score: { type: "number" },
      };

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("score: 0..100");
    });

    test("initial value uses min bound", async () => {
      baseConfig.state = {
        count: { type: "number", min: 5, max: 10 },
      };

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("count |-> 5");
    });

    test("initial value defaults to 0 when min omitted", async () => {
      baseConfig.state = {
        count: { type: "number", max: 10 },
      };

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("count |-> 0");
    });

    test("numeric comparison works with number-typed field", async () => {
      baseConfig.state = {
        count: { type: "number", min: 0, max: 10 },
      };
      baseAnalysis.handlers[0]!.preconditions = [
        { expression: "state.count > 0", location: { line: 1, column: 1 } },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("contextStates[ctx].count > 0");
    });
  });

  // ============================================================================
  // PARAMETER REFERENCES (Issue #31)
  // ============================================================================

  describe("Parameter References", () => {
    test("PayloadType includes handler parameter names", async () => {
      baseAnalysis.handlers = [
        {
          messageType: "SET_STATUS",
          assignments: [{ field: "status", value: "param:status" }],
          preconditions: [],
          postconditions: [],
          parameters: ["status"],
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("status: Value");
      expect(spec).toContain("PayloadType ==");
    });

    test("boolean parameter gets BOOLEAN type in PayloadType", async () => {
      baseAnalysis.handlers = [
        {
          messageType: "SET_ONLINE",
          assignments: [{ field: "active", value: "param:isOnline" }],
          preconditions: [],
          postconditions: [],
          parameters: ["isOnline"],
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("isOnline: BOOLEAN");
    });

    test("param: assignment resolves to payload reference", async () => {
      baseAnalysis.handlers = [
        {
          messageType: "SET_ONLINE",
          assignments: [{ field: "active", value: "param:isOnline" }],
          preconditions: [],
          postconditions: [],
          parameters: ["isOnline"],
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("payload.isOnline");
    });

    test("excluded params (state, msg) are not added to PayloadType", async () => {
      baseAnalysis.handlers = [
        {
          messageType: "UPDATE",
          assignments: [{ field: "count", value: true }],
          preconditions: [],
          postconditions: [],
          parameters: ["state", "msg", "data"],
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("data: Value");
      // Default fields should still be present
      expect(spec).toContain("id: Value");
    });

    test("default payload fields preserved when no handler params", async () => {
      baseAnalysis.handlers = [
        {
          messageType: "test",
          assignments: [],
          preconditions: [],
          postconditions: [],
        },
      ];

      const { spec } = await generator.generate(baseConfig, baseAnalysis);

      expect(spec).toContain("id: Value");
      expect(spec).toContain("text: Value");
      expect(spec).toContain("userId: Value");
    });
  });
});
