// Issue #74 — ensures() emits a step-temporal property, NOT an Assert
// conjunct in the action body. With Assert as a conjunct, TLC's action
// evaluator treats a failing predicate as "this binding isn't a successor"
// and the buggy transition simply doesn't fire (wrong-target writes pass
// verification silently). The fix lifts each handler's postconditions
// into `EnsuresAfter_<HandlerName> == [][P]_allVars` in the PROPERTIES
// section, where TLC checks them as a step-level safety property.
//
// These tests pin the generated spec syntax. The end-to-end check that
// proves a wrong-target mutation actually fails under TLC lives next to
// the runner integration tests.

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

describe("ensures() emits a step-temporal property (issue #74)", () => {
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

  test("the action body no longer carries the postcondition as an Assert conjunct", async () => {
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

    // The Assert-in-action-body shape (issue #73's incomplete fix) must
    // not appear: that was the failure mode #74 documents.
    expect(spec).not.toContain(`/\\ Assert(contextStates'[ctx]`);
  });

  test("each handler with postconditions emits a step-temporal property", async () => {
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

    // Property name follows the EnsuresAfter_<actionName> convention.
    expect(spec).toContain("EnsuresAfter_HandleDisconnect == [][");
    // The predicate fires on the (s, s') pair that just delivered a
    // matching message, and reads the post-state via contextStates'.
    expect(spec).toContain('messages[m].status = "pending"');
    expect(spec).toContain('messages\'[m].status = "delivered"');
    expect(spec).toContain('messages[m].msgType = "DISCONNECT"');
    expect(spec).toContain(`contextStates'[target].phase = "disconnected"`);
    // Step-temporal — `[][P]_allVars` is a safety property, no liveness
    // machinery needed.
    expect(spec).toContain("]_allVars");
  });

  test("multiple ensures on one handler combine into a single property", async () => {
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

    // Both predicates appear, in the post-state form, under the single
    // EnsuresAfter_HandleDisconnect property — one definition.
    const matches = spec.match(/EnsuresAfter_HandleDisconnect ==/g) ?? [];
    expect(matches.length).toBe(1);
    expect(spec).toContain(`contextStates'[target].phase = "disconnected"`);
    expect(spec).toContain(`contextStates'[target].phase # "connecting"`);
  });

  test("wrong-target mutation: spec syntactically distinguishes the EXCEPT write from the property predicate", async () => {
    // The shape #74 names: EXCEPT writes the wrong target; the property
    // predicate references the right one. With ensures-as-conjunct (the
    // 0.33–0.34 implementation), TLC silently disabled the action and
    // reported PASS. With ensures-as-property, the EXCEPT can fire and
    // the property check runs against the resulting state — failure
    // surfaces as a real counterexample.
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        // bug: handler writes "connecting" instead of "disconnected"
        assignments: [{ field: "phase", value: "connecting" }],
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

    // The wrong EXCEPT write is in the action body…
    expect(spec).toContain(`![ctx].phase = "connecting"`);
    // …and the property predicate (post-state, checked AFTER the write)
    // expects the right value. TLC will fire the action, then check the
    // property, then report the violation.
    expect(spec).toContain(`contextStates'[target].phase = "disconnected"`);
    // Crucially the predicate is NOT a conjunct in the action body, so
    // TLC won't silently disable HandleDisconnect when it fires the
    // wrong write.
    expect(spec).not.toContain(`/\\ Assert(contextStates'[ctx]`);
  });

  test("the property is registered in the cfg PROPERTIES section", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
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

    const { cfg } = await generator.generate(baseConfig, baseAnalysis);

    expect(cfg).toContain("PROPERTIES");
    expect(cfg).toContain("EnsuresAfter_HandleDisconnect");
  });

  test("module-end marker is the last non-empty line of the spec", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "DISCONNECT",
        assignments: [{ field: "phase", value: "disconnected" }],
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

    // Temporal properties must appear inside the module, not after its
    // closing line. Take the position of the property header and the
    // last `=====` and compare.
    const propHeaderIdx = spec.indexOf("EnsuresAfter_HandleDisconnect");
    const lastEquals = spec.lastIndexOf(
      "============================================================================="
    );
    expect(propHeaderIdx).toBeGreaterThan(0);
    expect(lastEquals).toBeGreaterThan(propHeaderIdx);
  });

  test("a handler with no postconditions does not create a property", async () => {
    baseAnalysis.handlers = [
      {
        messageType: "PING",
        assignments: [{ field: "phase", value: "connecting" }],
        preconditions: [],
        postconditions: [],
      },
    ];

    const { spec, cfg } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).not.toContain("EnsuresAfter_HandlePing");
    expect(cfg).not.toContain("EnsuresAfter_HandlePing");
  });

  test("double-quote in user-supplied message survives into the property description comment", async () => {
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

    // The description appears as a TLA+ comment so embedded quotes do
    // not need escaping the way Assert-string-arg quotes did.
    expect(spec).toContain(`\\* ensures(...) for DISCONNECT`);
  });
});
