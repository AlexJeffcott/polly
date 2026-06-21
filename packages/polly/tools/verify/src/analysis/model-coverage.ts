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

import type { OffSurfaceMutation } from "../core/model";
import type { MessageHandler } from "../types";

/** polly#163: one verified-state write outside the modelled handler surface. */
export type OffSurfaceWriter = {
  /** Enclosing function/method, e.g. `RecoveryFlow.register`, or `<module>`. */
  function: string;
  file: string;
  line: number;
};

/** Per declared field: the message types of every handler that assigns it. */
export type FieldWriteCoverage = {
  /** The declared (config) field name, canonical dot-form. */
  field: string;
  /** Message types of handlers that write this field (sorted, de-duplicated). */
  writers: string[];
  /**
   * polly#163: writers of this field that escape the modelled handler surface
   * (non-dispatched functions/methods). Present only when there is at least one;
   * a field with these is mutated by a path no TLA action explores, even if a
   * handler also writes it (the case `unwrittenFields` cannot see).
   */
  offSurfaceWriters?: OffSurfaceWriter[];
};

/**
 * polly#163: a verified-state write the model never explores, tagged with
 * whether it lands on a declared field (the dangerous, fail-closed case) or an
 * undeclared one (reported as a plain warning).
 */
export type OffSurfaceFinding = {
  /** Canonical config field name when declared, else the raw `${signal}_field`. */
  field: string;
  signalVariable: string;
  function: string;
  file: string;
  line: number;
  /** True when `field` is part of the declared verified-state schema. */
  declared: boolean;
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
   * polly#163: every verified-state write outside the modelled handler surface.
   * Ones whose `declared` flag is set land on a field in the verified schema —
   * the model carries that field but a non-dispatched path mutates it, which
   * `unwrittenFields` cannot detect when a handler also writes the field.
   */
  offSurfaceMutations: OffSurfaceFinding[];
  /**
   * True when the model has a coverage gap worth failing `--strict` on: a
   * declared-but-unwritten field (the model cannot exercise it) OR a declared
   * field mutated off-surface (polly#163 — a path no transition explores).
   * Unconstrained mutators are a soft hint and never set this.
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
 * polly#163: turn raw off-surface mutations into the report's per-field writer
 * lists and finding list. Only writes that land on a DECLARED field are kept —
 * for an undeclared signal there is no modelled transition to be "outside" of,
 * so those are dropped rather than reported as noise. `rawByKey` maps a
 * normalised field key to its original config name.
 */
function foldOffSurface(
  offSurface: OffSurfaceMutation[],
  rawByKey: Map<string, string>
): {
  offSurfaceByField: Map<string, OffSurfaceWriter[]>;
  offSurfaceMutations: OffSurfaceFinding[];
} {
  const offSurfaceByField = new Map<string, OffSurfaceWriter[]>();
  const offSurfaceMutations: OffSurfaceFinding[] = [];
  for (const m of offSurface) {
    const key = norm(m.field);
    const raw = rawByKey.get(key);
    if (raw === undefined) continue;
    offSurfaceMutations.push({
      field: raw,
      signalVariable: m.signalVariable,
      function: m.functionName,
      file: m.filePath,
      line: m.line,
      declared: true,
    });
    const list = offSurfaceByField.get(key) ?? [];
    list.push({ function: m.functionName, file: m.filePath, line: m.line });
    offSurfaceByField.set(key, list);
  }
  return { offSurfaceByField, offSurfaceMutations };
}

/**
 * Compute model coverage of the declared state schema by the analyzed handler
 * surface. `stateFields` are the keys of the verification config's `state`
 * block; `handlers` is `analysis.handlers` (already filtered to representable
 * message types upstream); `offSurface` is `analysis.offSurfaceMutations`
 * (polly#163) — verified-state writes the extractor found outside every
 * modelled handler body. It defaults to empty so existing callers are
 * unaffected.
 */
export function computeModelCoverage(
  stateFields: string[],
  handlers: MessageHandler[],
  offSurface: OffSurfaceMutation[] = []
): ModelCoverageReport {
  // declared field (normalised) -> set of writer message types
  const writersByField = new Map<string, Set<string>>();
  for (const field of stateFields) {
    writersByField.set(norm(field), new Set());
  }

  // declared field (normalised) -> original config name, preserving order
  const declaredOrder = stateFields.map((f) => ({ raw: f, key: norm(f) }));
  const rawByKey = new Map(declaredOrder.map((d) => [d.key, d.raw]));

  for (const handler of handlers) {
    for (const assignment of handler.assignments) {
      const key = norm(assignment.field);
      const writers = writersByField.get(key);
      if (writers) writers.add(handler.messageType);
    }
  }

  // polly#163: fold off-surface writers in per declared field.
  const { offSurfaceByField, offSurfaceMutations } = foldOffSurface(offSurface, rawByKey);

  const fieldCoverage: FieldWriteCoverage[] = declaredOrder.map(({ raw, key }) => {
    const offSurfaceWriters = offSurfaceByField.get(key);
    return {
      field: raw,
      writers: Array.from(writersByField.get(key) ?? []).sort(),
      ...(offSurfaceWriters && offSurfaceWriters.length > 0 ? { offSurfaceWriters } : {}),
    };
  });

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

  const hasDeclaredOffSurface = offSurfaceMutations.some((m) => m.declared);

  return {
    fieldCoverage,
    unwrittenFields,
    unconstrainedMutators,
    offSurfaceMutations,
    hasStrictViolation: unwrittenFields.length > 0 || hasDeclaredOffSurface,
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
  if (report.unwrittenFields.length > 0) {
    reasons.push(
      `${report.unwrittenFields.length} declared state field(s) written by no modelled handler`
    );
  }
  // polly#163: a declared field mutated by a non-dispatched path the model never
  // explores. Distinct from unwrittenFields — this fires even when a handler
  // also writes the field.
  const declaredOffSurface = (report.offSurfaceMutations ?? []).filter((m) => m.declared);
  if (declaredOffSurface.length > 0) {
    reasons.push(
      `${declaredOffSurface.length} declared state field write(s) outside any modelled transition (polly#163)`
    );
  }
  if (meshFindingCount > 0) {
    reasons.push(`${meshFindingCount} unverified $meshState/$peerState predicate(s)`);
  }
  return reasons;
}
