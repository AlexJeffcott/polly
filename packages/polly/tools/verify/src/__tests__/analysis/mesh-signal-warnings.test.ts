// polly#117: tests for the mesh/peer signal warning finder. A
// $meshState doc declared under `mesh:` in the verification config is
// verified cross-peer and must NOT be warned about; an undeclared
// $meshState signal, or any $peerState signal, must be reported.

import { describe, expect, test } from "bun:test";
import { computeMeshOrPeerSignalFindings } from "../../analysis/mesh-signal-warnings";
import type { CodebaseAnalysis, MeshOrPeerSignalInfo, MessageHandler } from "../../core/model";

function handler(
  messageType: string,
  preconditions: Array<{ expression: string }>,
  postconditions: Array<{ expression: string }>
): MessageHandler {
  return {
    messageType,
    node: "background",
    assignments: [],
    preconditions: preconditions.map((p) => ({
      expression: p.expression,
      location: { line: 10, column: 1 },
    })),
    postconditions: postconditions.map((p) => ({
      expression: p.expression,
      location: { line: 20, column: 1 },
    })),
    location: { file: "/fixture/handlers.ts", line: 5 },
  };
}

function analysis(
  handlers: MessageHandler[],
  meshOrPeerSignals: MeshOrPeerSignalInfo[]
): CodebaseAnalysis {
  return {
    stateType: null,
    messageTypes: handlers.map((h) => h.messageType),
    fields: [],
    handlers,
    stateConstraints: [],
    meshOrPeerSignals,
  };
}

const meshSignal = (variableName: string, key: string): MeshOrPeerSignalInfo => ({
  kind: "mesh",
  key,
  variableName,
  filePath: "/fixture/state.ts",
  line: 1,
});

const peerSignal = (variableName: string, key: string): MeshOrPeerSignalInfo => ({
  kind: "peer",
  key,
  variableName,
  filePath: "/fixture/state.ts",
  line: 1,
});

describe("computeMeshOrPeerSignalFindings (polly#117)", () => {
  test("reports an undeclared $meshState signal referenced in an ensures", () => {
    const a = analysis(
      [handler("SET", [], [{ expression: "doc.value.count === 3" }])],
      [meshSignal("doc", "doc-id")]
    );
    const findings = computeMeshOrPeerSignalFindings(a, new Set());

    expect(findings).toHaveLength(1);
    expect(findings[0]?.signalKind).toBe("mesh");
    expect(findings[0]?.signalName).toBe("doc");
    expect(findings[0]?.kind).toBe("postcondition");
    expect(findings[0]?.handler).toBe("SET");
  });

  test("does NOT report a $meshState signal whose key is declared in config.mesh", () => {
    const a = analysis(
      [handler("SET", [], [{ expression: "doc.value.count === 3" }])],
      [meshSignal("doc", "doc-id")]
    );
    const findings = computeMeshOrPeerSignalFindings(a, new Set(["doc-id"]));

    expect(findings).toHaveLength(0);
  });

  test("reports a $peerState signal even though it cannot be declared in config.mesh", () => {
    const a = analysis(
      [handler("CHECK", [{ expression: "presence.value.online === true" }], [])],
      [peerSignal("presence", "presence-id")]
    );
    // Even if the key collides with a declared mesh doc, a peer signal
    // is never excluded — there is no cross-peer model for $peerState.
    const findings = computeMeshOrPeerSignalFindings(a, new Set(["presence-id"]));

    expect(findings).toHaveLength(1);
    expect(findings[0]?.signalKind).toBe("peer");
    expect(findings[0]?.kind).toBe("precondition");
  });

  test("with a mix, reports only the undeclared mesh signal", () => {
    const a = analysis(
      [
        handler(
          "SET",
          [],
          [
            { expression: "declared.value.count === 1" },
            { expression: "undeclared.value.count === 2" },
          ]
        ),
      ],
      [meshSignal("declared", "declared-id"), meshSignal("undeclared", "undeclared-id")]
    );
    const findings = computeMeshOrPeerSignalFindings(a, new Set(["declared-id"]));

    expect(findings).toHaveLength(1);
    expect(findings[0]?.signalName).toBe("undeclared");
  });

  test("returns nothing when there are no mesh/peer signals", () => {
    const a = analysis([handler("SET", [], [{ expression: "local.value === 1" }])], []);
    expect(computeMeshOrPeerSignalFindings(a, new Set())).toHaveLength(0);
  });

  test("returns nothing when a mesh signal is declared but never referenced in a predicate", () => {
    const a = analysis([handler("SET", [], [])], [meshSignal("doc", "doc-id")]);
    expect(computeMeshOrPeerSignalFindings(a, new Set())).toHaveLength(0);
  });

  test("matches on an identifier boundary — `thing` does not fire on `myThing.value`", () => {
    const a = analysis(
      [handler("SET", [], [{ expression: "myThing.value.count === 3" }])],
      [meshSignal("thing", "thing-id")]
    );
    expect(computeMeshOrPeerSignalFindings(a, new Set())).toHaveLength(0);
  });

  test("reports the same signal once per referencing predicate", () => {
    const a = analysis(
      [
        handler(
          "SET",
          [{ expression: "doc.value.count > 0" }],
          [{ expression: "doc.value.count === 3" }]
        ),
      ],
      [meshSignal("doc", "doc-id")]
    );
    const findings = computeMeshOrPeerSignalFindings(a, new Set());

    expect(findings).toHaveLength(2);
    expect(findings.map((f) => f.kind).sort()).toEqual(["postcondition", "precondition"]);
  });
});
