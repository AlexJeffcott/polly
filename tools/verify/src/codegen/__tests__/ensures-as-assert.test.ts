// Issue #73 — ensures() emits TLC Assert so wrong-target transitions are
// flagged as hard errors instead of being silently treated as disabled actions.

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

describe("ensures() emits TLC Assert (issue #73)", () => {
  let generator: TLAGenerator;
  let baseConfig: VerificationConfig;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();
    baseConfig = {
      state: {
        phase: {
          type: "enum",
          values: ["disconnected", "connecting", "connected-leader"],
        },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      onBuild: "warn",
      onRelease: "error",
    };
    baseAnalysis = {
      stateType: null,
      messageTypes: ["test"],
      fields: [],
      handlers: [],
      stateConstraints: [],
    };
  });

  test("postcondition is wrapped in Assert with the user message", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            message: "phase must be disconnected after disconnect",
            location: { line: 1, column: 1 },
          },
        ],
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain(
      `/\\ Assert(contextStates'[ctx].phase = "disconnected", "phase must be disconnected after disconnect")`
    );
    // The bare conjunct form must NOT appear — that was the buggy behavior.
    expect(spec).not.toMatch(/\/\\\\ contextStates'\[ctx\]\.phase = "disconnected"\s*$/m);
  });

  test("postcondition without a user message uses a sensible default", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            location: { line: 1, column: 1 },
          },
        ],
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain(`Assert(contextStates'[ctx].phase = "disconnected", "ensures failed")`);
  });

  test("multiple ensures each emit their own Assert", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            message: "phase ok",
            location: { line: 1, column: 1 },
          },
          {
            expression: "state.phase !== 'connecting'",
            message: "not connecting",
            location: { line: 1, column: 1 },
          },
        ],
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    const asserts = spec.match(/\/\\\\ Assert\(/g) ?? spec.match(/\/\\ Assert\(/g);
    expect(asserts?.length ?? 0).toBeGreaterThanOrEqual(2);
    expect(spec).toContain(`"phase ok"`);
    expect(spec).toContain(`"not connecting"`);
  });

  test("wrong-target mutation: ensures Assert references the post-state", async () => {
    // Demonstrates the bug class #73 closes: the EXCEPT writes the wrong target,
    // and ensures Assert checks the correct one. The generated spec contains
    // both — the contradiction surfaces at TLC time as an Assert failure.
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "connecting" }], // bug: should be "disconnected"
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            message: "phase must be disconnected",
            location: { line: 1, column: 1 },
          },
        ],
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain(`![ctx].phase = "connecting"`);
    expect(spec).toContain(
      `/\\ Assert(contextStates'[ctx].phase = "disconnected", "phase must be disconnected")`
    );
  });

  test("double-quote in user message is escaped", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
        preconditions: [],
        postconditions: [
          {
            expression: "state.phase === 'disconnected'",
            message: 'phase = "disconnected"',
            location: { line: 1, column: 1 },
          },
        ],
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain(
      `Assert(contextStates'[ctx].phase = "disconnected", "phase = \\"disconnected\\"")`
    );
  });
});
