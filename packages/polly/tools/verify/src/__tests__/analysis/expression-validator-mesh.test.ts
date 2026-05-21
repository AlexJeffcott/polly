// polly#117: validateExpressions must not flag a reference into a
// $meshState/$peerState signal as an "unmodeled field". Those signals
// live in the mesh namespace (or are reported by the dedicated
// mesh/peer signal warning) — the state-config modeling check should
// leave them alone.

import { describe, expect, test } from "bun:test";
import { validateExpressions } from "../../analysis/expression-validator";
import type { MessageHandler } from "../../core/model";

function handlerWithEnsures(expression: string): MessageHandler {
  return {
    messageType: "BUMP",
    node: "background",
    assignments: [],
    preconditions: [],
    postconditions: [{ expression, location: { line: 12, column: 1 } }],
    location: { file: "/fixture/handlers.ts", line: 5 },
  };
}

const unmodeled = (r: { warnings: Array<{ kind: string }> }): number =>
  r.warnings.filter((w) => w.kind === "unmodeled_field").length;

describe("validateExpressions mesh-signal handling (polly#117)", () => {
  test("a mesh-signal reference is NOT flagged as an unmodeled field", () => {
    const handlers = [handlerWithEnsures("doc.value.count === 3")];
    const result = validateExpressions(handlers, {}, new Set(["doc"]));

    expect(unmodeled(result)).toBe(0);
  });

  test("the same reference IS flagged when not known as a mesh signal", () => {
    // Guards against a vacuous pass above — without the mesh-name set,
    // an undeclared field is still reported.
    const handlers = [handlerWithEnsures("doc.value.count === 3")];
    const result = validateExpressions(handlers, {});

    expect(unmodeled(result)).toBe(1);
  });

  test("a genuinely unmodeled non-mesh field is still flagged", () => {
    const handlers = [handlerWithEnsures("widget.value.size === 1")];
    const result = validateExpressions(handlers, {}, new Set(["doc"]));

    expect(unmodeled(result)).toBe(1);
  });

  test("a mesh reference inside forAllPeers is not flagged", () => {
    const handlers = [
      handlerWithEnsures("forAllPeers((peer) => peer.doc.value.count === doc.value.count)"),
    ];
    const result = validateExpressions(handlers, {}, new Set(["doc"]));

    expect(unmodeled(result)).toBe(0);
  });
});
