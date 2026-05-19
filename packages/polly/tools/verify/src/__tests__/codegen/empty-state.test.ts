import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../../analysis/src/types";
import { TLAGenerator } from "../../codegen/tla";
import type { VerificationConfig } from "../../types";

/**
 * Regression test for empty state bug
 * When config.state is empty, the generator was creating invalid TLA+:
 * State == [
 * ]
 *
 * This test ensures empty states generate valid TLA+ with a dummy field.
 */
describe("Empty State Handling", () => {
  test("should generate valid TLA+ when state is empty", async () => {
    const config: VerificationConfig = {
      state: {}, // Empty state
      messages: {
        maxInFlight: 3,
        maxTabs: 1,
      },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: ["query", "command"],
      fields: [],
      handlers: [
        {
          messageType: "query",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 1 },
        },
      ],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(config, analysis);
    const spec = result.spec;

    // Should NOT contain empty record syntax
    expect(spec).not.toContain("State == [\n]");
    expect(spec).not.toContain("InitialState == [\n]");

    // Should contain dummy field placeholder
    expect(spec).toContain("dummy: BOOLEAN");
    expect(spec).toContain("dummy |-> FALSE");

    // Should be valid TLA+ - no parse errors
    // The actual validation would be done by SANY, but we can check structure
    expect(spec).toMatch(/State == \[[\s\S]*?\]/);
    expect(spec).toMatch(/InitialState == \[[\s\S]*?\]/);
  });

  test("should generate normal TLA+ when state has fields", async () => {
    const config: VerificationConfig = {
      state: {
        count: { min: 0, max: 10 },
      },
      messages: {
        maxInFlight: 3,
        maxTabs: 1,
      },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: ["increment"],
      fields: [],
      handlers: [
        {
          messageType: "increment",
          node: "background",
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: "test.ts", line: 1 },
        },
      ],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(config, analysis);
    const spec = result.spec;

    // Should NOT contain dummy field
    expect(spec).not.toContain("dummy: BOOLEAN");
    expect(spec).not.toContain("dummy |-> FALSE");

    // Should contain actual state field
    expect(spec).toContain("count: 0..10");
    expect(spec).toContain("count |-> 0");
  });

  test("should handle state with only analysis fields (no config.state)", async () => {
    const config: VerificationConfig = {
      state: {},
      messages: {
        maxInFlight: 3,
        maxTabs: 1,
      },
      onBuild: "warn",
      onRelease: "error",
    };

    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: ["test"],
      fields: [
        {
          path: "counter",
          type: { kind: "number" },
          optional: false,
        },
      ],
      handlers: [],
    };

    const generator = new TLAGenerator();
    const result = await generator.generate(config, analysis);
    const spec = result.spec;

    // Should contain field from analysis
    expect(spec).toContain("counter:");

    // Should NOT contain dummy field since we have analysis fields
    expect(spec).not.toContain("dummy: BOOLEAN");
  });
});
