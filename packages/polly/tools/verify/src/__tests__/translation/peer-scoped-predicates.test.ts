// polly#117: cross-peer quantifier translation.
// Confirms that forAllPeers / somePeer wrappers in requires/ensures
// emit the corresponding TLA+ \A / \E quantifier over Contexts, with
// the binder's signal references rebound to contextStates[<binder>].

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../../analysis/src/types";
import { TLAGenerator } from "../../codegen/tla";

describe("Cross-peer quantifier translation (polly#117)", () => {
  let generator: TLAGenerator;
  let baseConfig: VerificationConfig;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();

    baseConfig = {
      state: {
        todos: { type: "enum", values: ["0", "1", "2"] },
      },
      messages: {
        maxInFlight: 2,
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

  test("forAllPeers emits a universal quantifier over Contexts \\ {target}", async () => {
    baseAnalysis.handlers[0]!.postconditions = [
      {
        expression: "forAllPeers(peer => peer.todos.value === todos.value)",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    // Inside EnsuresAfter_*, the codegen rebinds ctx -> target so the
    // quantifier excludes the delivery target rather than the executing
    // context. Both the [ctx] indexer and the {ctx} set-difference
    // exclusion are rebound.
    expect(spec).toContain("\\A peer \\in Contexts \\ {target}");
    expect(spec).toContain("contextStates'[peer].todos");
    expect(spec).toContain("contextStates'[target].todos");
  });

  test("somePeer emits an existential quantifier over Contexts \\ {ctx}", async () => {
    baseAnalysis.handlers[0]!.preconditions = [
      {
        expression: "somePeer(peer => peer.todos.value === todos.value)",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("\\E peer \\in Contexts \\ {ctx}");
    expect(spec).toContain("contextStates[peer].todos");
    expect(spec).toContain("contextStates[ctx].todos");
  });

  test("binder-prefixed signal with field path resolves correctly", async () => {
    baseAnalysis.handlers[0]!.postconditions = [
      {
        expression: "forAllPeers(peer => peer.user.value.loggedIn === true)",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("\\A peer \\in Contexts \\ {target}");
    expect(spec).toContain("contextStates'[peer].user_loggedIn");
  });

  test("plain predicate without wrapper is unchanged", async () => {
    baseAnalysis.handlers[0]!.preconditions = [
      { expression: "state.todos === 1", location: { line: 1, column: 1 } },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    // No forall/exists quantifier should appear from this predicate.
    expect(spec).toContain("contextStates[ctx].todos = 1");
  });

  test("custom binder name is honored", async () => {
    baseAnalysis.handlers[0]!.postconditions = [
      {
        expression: "forAllPeers(p => p.todos.value === todos.value)",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("\\A p \\in Contexts \\ {target}");
    expect(spec).toContain("contextStates'[p].todos");
  });
});
