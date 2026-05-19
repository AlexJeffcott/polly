// polly#117: mesh-state codegen — declaring `mesh: { docId: { fields } }`
// in the verification config switches signal references in
// requires/ensures/assignments from `contextStates[ctx]` to
// `meshState[ctx][docId]`, emits a PropagateMeshOp action, and
// integrates with `forAllPeers` for genuine cross-peer claims.

import { beforeEach, describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../../analysis/src/types";
import { TLAGenerator } from "../../codegen/tla";

describe("Mesh-state codegen (polly#117)", () => {
  let generator: TLAGenerator;
  let baseConfig: VerificationConfig;
  let baseAnalysis: CodebaseAnalysis;

  beforeEach(() => {
    generator = new TLAGenerator();
    baseConfig = {
      state: {},
      mesh: {
        todos: {
          entries: { type: "number", min: 0, max: 3 },
        },
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
      meshOrPeerSignals: [
        {
          kind: "mesh",
          key: "todos",
          variableName: "todos",
          filePath: "/fixture/state.ts",
          line: 1,
        },
      ],
    };
  });

  test("declares MeshDocs, doc record type, and InitialMesh", async () => {
    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain('MeshDocs == {"todos"}');
    expect(spec).toContain("MeshDoc_todos == [entries: 0..3]");
    expect(spec).toContain("InitialMesh == [");
    expect(spec).toContain('"todos" |-> [entries |-> 0]');
  });

  test("declares meshState variable and initializes it per context", async () => {
    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("VARIABLE meshState");
    expect(spec).toContain("meshState = [c \\in Contexts |-> InitialMesh]");
    expect(spec).toContain("allVars == <<");
    // allVars list must include meshState
    expect(spec).toMatch(/allVars == <<[^>]*meshState[^>]*>>/);
  });

  test("emits PropagateMeshOp and includes it in UserNext", async () => {
    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("PropagateMeshOp(src, dst, docId) ==");
    expect(spec).toContain("meshState[src][docId] # meshState[dst][docId]");
    expect(spec).toContain(
      "meshState' = [meshState EXCEPT ![dst][docId] = meshState[src][docId]]"
    );
    expect(spec).toContain(
      "\\E src, dst \\in Contexts : \\E docId \\in MeshDocs : PropagateMeshOp(src, dst, docId)"
    );
  });

  test("routes a $meshState reference in a precondition through meshState", async () => {
    baseAnalysis.handlers[0]!.preconditions = [
      {
        expression: "todos.value.entries === 0",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain('meshState[ctx]["todos"].entries = 0');
    // The mesh routing should not also produce a contextStates flat field
    expect(spec).not.toContain("contextStates[ctx].todos_entries = 0");
  });

  test("routes a $meshState reference in an ensures through meshState (primed)", async () => {
    baseAnalysis.handlers[0]!.postconditions = [
      {
        expression: "todos.value.entries === 3",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain('meshState\'[target]["todos"].entries = 3');
  });

  test("forAllPeers reference to a $meshState signal routes through meshState[<binder>]", async () => {
    baseAnalysis.handlers[0]!.postconditions = [
      {
        expression: "forAllPeers(peer => peer.todos.value.entries === todos.value.entries)",
        location: { line: 1, column: 1 },
      },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("\\A peer \\in Contexts \\ {target}");
    expect(spec).toContain('meshState\'[peer]["todos"].entries');
    expect(spec).toContain('meshState\'[target]["todos"].entries');
  });

  test("$sharedState signals continue to flatten into contextStates (backward compat)", async () => {
    // Config has both a $sharedState field and a $meshState signal
    baseConfig.state = { localFlag: { type: "boolean" } };
    baseAnalysis.handlers[0]!.preconditions = [
      { expression: "localFlag.value === true", location: { line: 1, column: 1 } },
    ];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain("contextStates[ctx].localFlag = TRUE");
  });

  test("assigning to a $meshState signal field writes meshState' EXCEPT", async () => {
    baseAnalysis.handlers[0]!.assignments = [{ field: "todos_entries", value: 2 }];

    const { spec } = await generator.generate(baseConfig, baseAnalysis);

    expect(spec).toContain('meshState\' = [meshState EXCEPT ![ctx]["todos"].entries = 2]');
    // No accidental write to contextStates for a mesh-routed field
    expect(spec).not.toContain("contextStates' = [contextStates EXCEPT ![ctx].todos_entries");
  });

  test("config without mesh declaration: spec is unchanged from legacy shape", async () => {
    const config: VerificationConfig = {
      state: { localFlag: { type: "boolean" } },
      messages: { maxInFlight: 2, maxTabs: 1 },
    };
    const analysis: CodebaseAnalysis = {
      stateType: null,
      messageTypes: ["test"],
      fields: [],
      handlers: [
        { messageType: "test", assignments: [], preconditions: [], postconditions: [] },
      ],
      stateConstraints: [],
    };

    const { spec } = await generator.generate(config, analysis);

    expect(spec).not.toContain("VARIABLE meshState");
    expect(spec).not.toContain("PropagateMeshOp");
    expect(spec).not.toContain("MeshDocs");
  });
});
