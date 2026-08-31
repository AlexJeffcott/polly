// Integration tests for temporal properties.
//
// The invariant half of this file went with the JSDoc `@invariant` extractor in
// polly#168: it drove `enableInvariants: true`, a flag no production caller set,
// so it covered a mechanism the shipped code never reached. `capabilities` is
// the live path and is covered by codegen/__tests__/capability-invariants.ts.

import { describe, expect, test } from "bun:test";
import { TLAGenerator } from "../../codegen/tla";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";

describe("Property Integration", () => {
  const baseConfig: VerificationConfig = {
    state: {
      count: { type: "enum", values: ["0", "1", "2"] },
    },
    messages: {
      maxInFlight: 3,
      maxTabs: 1,
    },
  };

  const baseAnalysis: CodebaseAnalysis = {
    messageTypes: ["increment", "reset"],
    handlers: [
      {
        messageType: "increment",
        node: "test",
        assignments: [
          {
            field: "count",
            value: "1",
          },
        ],
        preconditions: [],
        postconditions: [],
      },
    ],
    fields: [{ name: "count", type: "number" }],
    typeDefinitions: [],
  };

  // Temporal Property Integration Tests

  test("generates spec without temporal properties when disabled", async () => {
    const generator = new TLAGenerator();

    const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).not.toContain("Temporal Properties");
    expect(spec).not.toContain("VARIABLE delivered");
    expect(cfg).not.toContain("PROPERTIES");
  });

  test("generates temporal properties when enabled", async () => {
    const analysisWithPatterns: CodebaseAnalysis = {
      messageTypes: ["init", "request", "response"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator({
      enableTemporalProperties: true,
    });

    const { spec, cfg } = await generator.generate(baseConfig, analysisWithPatterns);

    // Should have temporal properties section
    expect(spec).toContain("Temporal Properties");

    // Should have delivered tracking
    expect(spec).toContain("VARIABLE delivered");
    expect(spec).toContain("InitDelivered");
    expect(spec).toContain("MarkDelivered");

    // Should have init-first property
    expect(spec).toContain("InitMessageFirst");

    // Should have request-response property
    expect(spec).toContain("EventuallyGets");

    // Config should list properties
    expect(cfg).toContain("PROPERTIES");
  });

  test("generates multiple temporal properties", async () => {
    const analysisWithMultiplePatterns: CodebaseAnalysis = {
      messageTypes: ["init", "request", "response", "query", "result", "start", "complete"],
      handlers: [],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator({
      enableTemporalProperties: true,
    });

    const { spec, cfg } = await generator.generate(baseConfig, analysisWithMultiplePatterns);

    // Should detect multiple patterns
    expect(spec).toContain("RequestEventuallyGetsResponse");
    expect(spec).toContain("QueryEventuallyGetsResult");
    expect(spec).toContain("EventuallyCompletes");

    // Config should list all properties
    const propCount = (cfg.match(/PROPERTIES/g) || []).length;
    expect(propCount).toBeGreaterThanOrEqual(1);
  });

  test("generates ordering properties from handler preconditions", async () => {
    const analysisWithAuth: CodebaseAnalysis = {
      messageTypes: ["login", "updateProfile"],
      handlers: [
        {
          messageType: "updateProfile",
          node: "test",
          preconditions: [
            {
              expression: "state.authenticated === true",
              location: { line: 1, column: 1 },
            },
          ],
          assignments: [],
          postconditions: [],
        },
      ],
      fields: [],
      typeDefinitions: [],
    };

    const generator = new TLAGenerator({
      enableTemporalProperties: true,
    });

    const { spec } = await generator.generate(baseConfig, analysisWithAuth);

    expect(spec).toContain("RequiresLogin");
  });

  test("maintains backward compatibility when features disabled", async () => {
    const generator = new TLAGenerator();

    const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

    // Should still generate valid TLA+
    expect(spec).toContain("MODULE UserApp");
    expect(spec).toContain("EXTENDS MessageRouter");
    expect(spec).toContain("UserStateTypeInvariant");

    // Config should be standard format
    expect(cfg).toContain("SPECIFICATION UserSpec");
    expect(cfg).toContain("INVARIANTS");
    expect(cfg).toContain("TypeOK");
  });
});
