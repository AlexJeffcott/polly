// polly#160 (Ask #1): model-coverage report — surface what the model does NOT
// cover instead of dropping it silently.
//
// The motivating bug (a capability granted by a path the model never sees) is an
// OMISSION: a statement never written, a transition never modelled. Mutation
// testing is blind to it (no line to mutate) and a green TLC run says nothing
// about a field no handler touches. This module reads the analyzed handler
// surface against the declared state schema and reports three things:
//
//   1. write distribution — for each declared state field, which handlers
//      assign it (the "written by some paths but not others" signal: the
//      scattered-invariant smell shows up as an uneven writer set).
//   2. unwritten fields — declared state fields NO modelled handler assigns.
//      The model carries a variable no transition can ever change: either dead
//      state inflating the state space, or — the dangerous case — a field whose
//      real mutating path was never modelled (e.g. a `register()` that escapes
//      the message-handler surface). This is the soundest static proxy for the
//      omission bug, so it is the `--strict` fail-closed trigger.
//   3. unconstrained mutators — handlers that mutate declared state but pin no
//      `ensures()` postcondition. The checker explores the transition but
//      asserts nothing about its effect. Reported as a hint (ensures is
//      optional by design), never a strict failure.
//
// `analysis.handlers` contains only handlers whose message type is representable
// in TLA+; the unrepresentable ones (polly#144) are filtered upstream and warned
// unconditionally there, so they are not re-reported here.

import type { MessageHandler } from "../types";

/** Per declared field: the message types of every handler that assigns it. */
export type FieldWriteCoverage = {
  /** The declared (config) field name, canonical dot-form. */
  field: string;
  /** Message types of handlers that write this field (sorted, de-duplicated). */
  writers: string[];
};

/** A handler that mutates declared state but states no postcondition. */
export type UnconstrainedMutator = {
  /** The handler's message type. */
  handler: string;
  /** Declared fields this handler assigns. */
  fields: string[];
  /** Source location of the handler. */
  location: { file: string; line: number };
};

export type ModelCoverageReport = {
  /** Write distribution for every declared field, in declaration order. */
  fieldCoverage: FieldWriteCoverage[];
  /** Declared fields no modelled handler assigns. */
  unwrittenFields: string[];
  /** Handlers that mutate declared state with no `ensures()` postcondition. */
  unconstrainedMutators: UnconstrainedMutator[];
  /**
   * True when the model has a coverage gap worth failing `--strict` on. Gated
   * on `unwrittenFields` only: a declared-but-unwritten field is an unambiguous
   * "the model cannot exercise this" signal. Unconstrained mutators are a soft
   * hint and never set this.
   */
  hasStrictViolation: boolean;
};

/** Canonical dot-form so a config field name and a handler assignment field
 *  compare equal regardless of underscore/dot form (assignments are dotted
 *  "user.loggedIn"; config keys may be underscore "user_loggedIn"). Mirrors
 *  the matcher in coupled-fields.ts. */
function norm(field: string): string {
  return field.replace(/_/g, ".");
}

/**
 * Compute model coverage of the declared state schema by the analyzed handler
 * surface. `stateFields` are the keys of the verification config's `state`
 * block; `handlers` is `analysis.handlers` (already filtered to representable
 * message types upstream).
 */
export function computeModelCoverage(
  stateFields: string[],
  handlers: MessageHandler[]
): ModelCoverageReport {
  // declared field (normalised) -> set of writer message types
  const writersByField = new Map<string, Set<string>>();
  for (const field of stateFields) {
    writersByField.set(norm(field), new Set());
  }

  // declared field (normalised) -> original config name, preserving order
  const declaredOrder = stateFields.map((f) => ({ raw: f, key: norm(f) }));

  for (const handler of handlers) {
    for (const assignment of handler.assignments) {
      const key = norm(assignment.field);
      const writers = writersByField.get(key);
      if (writers) writers.add(handler.messageType);
    }
  }

  const fieldCoverage: FieldWriteCoverage[] = declaredOrder.map(({ raw, key }) => ({
    field: raw,
    writers: Array.from(writersByField.get(key) ?? []).sort(),
  }));

  const unwrittenFields = fieldCoverage.filter((f) => f.writers.length === 0).map((f) => f.field);

  const declaredKeys = new Set(declaredOrder.map((d) => d.key));
  const unconstrainedMutators: UnconstrainedMutator[] = [];
  for (const handler of handlers) {
    if (handler.postconditions.length > 0) continue;
    const fields = Array.from(
      new Set(handler.assignments.map((a) => norm(a.field)).filter((f) => declaredKeys.has(f)))
    ).sort();
    if (fields.length > 0) {
      unconstrainedMutators.push({
        handler: handler.messageType,
        fields,
        location: handler.location,
      });
    }
  }

  return {
    fieldCoverage,
    unwrittenFields,
    unconstrainedMutators,
    hasStrictViolation: unwrittenFields.length > 0,
  };
}

/**
 * The reasons a `--strict` run should fail closed: an unwritten declared field
 * (a modelled-but-unreachable mutation — the omission class) and/or unverified
 * `$meshState`/`$peerState` predicates (polly#117). Empty array means strict
 * passes. Pure so the CLI's exit decision is testable apart from `process.exit`.
 */
export function strictCoverageReasons(
  report: ModelCoverageReport,
  meshFindingCount: number
): string[] {
  const reasons: string[] = [];
  if (report.hasStrictViolation) {
    reasons.push(
      `${report.unwrittenFields.length} declared state field(s) written by no modelled handler`
    );
  }
  if (meshFindingCount > 0) {
    reasons.push(`${meshFindingCount} unverified $meshState/$peerState predicate(s)`);
  }
  return reasons;
}
