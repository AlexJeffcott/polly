// polly#117: detect requires/ensures predicates whose cross-peer
// semantics the verifier does NOT check.
//
// A `$meshState` document is verified cross-peer only when its key is
// declared in the `mesh: { ... }` block of the verification config:
// the codegen then routes it through the `meshState` namespace, emits
// a `PropagateMeshOp` action, and lets `forAllPeers(...)` claims over
// it be checked. An *undeclared* `$meshState` signal — or any
// `$peerState` signal, for which no cross-peer model exists yet — is
// flattened to single-context local state, so a predicate over it
// silently asserts only the executing context's view.
//
// This module computes the findings; `cli.ts` renders them. Keeping
// the computation pure makes it directly testable without driving the
// whole CLI.

import type { CodebaseAnalysis } from "../core/model";

/** One predicate that references a signal with unverified cross-peer semantics. */
export type MeshOrPeerSignalFinding = {
  /** The handler (message type) the predicate belongs to. */
  handler: string;
  /** Whether the predicate is a requires() or an ensures(). */
  kind: "precondition" | "postcondition";
  /** The raw predicate expression. */
  expression: string;
  /** The offending signal's variable name. */
  signalName: string;
  /** Whether the signal is a `$meshState` or `$peerState` signal. */
  signalKind: "mesh" | "peer";
  /** Source location of the predicate. */
  location: { file: string; line: number };
};

/**
 * Find every requires/ensures predicate that references a
 * `$meshState`/`$peerState` signal the verifier does not check
 * cross-peer.
 *
 * A `$meshState` signal whose key is in `declaredMeshDocs` (i.e. the
 * consumer declared it under `mesh:` in the verification config) is
 * routed through the `meshState` namespace and IS verified — it is
 * excluded. Every other reference — an undeclared `$meshState` signal,
 * or any `$peerState` signal — is reported.
 *
 * @param analysis the analysed codebase
 * @param declaredMeshDocs the set of doc keys declared under `mesh:`
 *   in the verification config
 */
export function computeMeshOrPeerSignalFindings(
  analysis: CodebaseAnalysis,
  declaredMeshDocs: ReadonlySet<string>
): MeshOrPeerSignalFinding[] {
  const signals = analysis.meshOrPeerSignals ?? [];
  if (signals.length === 0) return [];

  // A declared $meshState doc is genuinely verified cross-peer; only
  // the rest are unverified and worth warning about.
  const unverified = signals.filter((s) => !(s.kind === "mesh" && declaredMeshDocs.has(s.key)));
  if (unverified.length === 0) return [];

  const findings: MeshOrPeerSignalFinding[] = [];

  for (const handler of analysis.handlers) {
    const scan = (
      conditions: Array<{ expression: string; location?: { line?: number } }>,
      kind: "precondition" | "postcondition"
    ): void => {
      for (const cond of conditions) {
        for (const sig of unverified) {
          // Match `<varName>.value` on an identifier boundary so a
          // signal named `thing` does not false-positive on
          // `myThing.value`.
          const pattern = new RegExp(`\\b${sig.variableName}\\.value\\b`);
          if (pattern.test(cond.expression)) {
            findings.push({
              handler: handler.messageType,
              kind,
              expression: cond.expression,
              signalName: sig.variableName,
              signalKind: sig.kind,
              location: {
                file: handler.location?.file ?? sig.filePath,
                line: cond.location?.line ?? handler.location?.line ?? sig.line,
              },
            });
          }
        }
      }
    };
    scan(handler.preconditions, "precondition");
    scan(handler.postconditions, "postcondition");
  }

  return findings;
}
