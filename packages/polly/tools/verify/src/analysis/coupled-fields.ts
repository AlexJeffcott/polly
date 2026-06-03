// polly#160 (A2): coupled-field write-coupling lint.
//
// A `coupledFields` group declares state fields that are expected to move
// together. Any single handler that writes a NON-EMPTY STRICT SUBSET of a
// group's fields in one transition is flagged — the smell behind "a capability
// granted without its precondition" (e.g. a handler that sets `authReady`
// without `authenticated`).
//
// This is a fast, syntactic, per-handler hint. It WARNS, never fails: a
// legitimate staged transition (handler X sets one field, handler Y sets the
// other) trips it as a false positive, so the caller prints warnings only. The
// sound, whole-reachable-state detector is the `capabilities` TLA+ invariant.

import type { MessageHandler } from "../types";

export type CoupledFieldsViolation = {
  /** The declared coupling group that was violated. */
  group: string[];
  /** The handler (message type) that wrote a strict subset of the group. */
  handler: string;
  /** Group fields this handler actually wrote. */
  written: string[];
  /** Group fields this handler did NOT write. */
  missing: string[];
};

export type CoupledFieldsResult = {
  valid: boolean;
  violations: CoupledFieldsViolation[];
};

/** Canonical dot-form so a config field name and a handler assignment field
 *  compare equal regardless of underscore/dot form (assignments are dotted
 *  "user.loggedIn"; config keys may be underscore "user_loggedIn"). */
function norm(field: string): string {
  return field.replace(/_/g, ".");
}

/**
 * Flag any handler that writes a non-empty strict subset of a coupled group.
 * Order within a group is irrelevant (set membership). Consumes ONLY the
 * explicit `coupledFields` groups — capability declarations are checked
 * separately by their generated TLA+ invariant.
 */
export function checkCoupledFields(
  coupledFields: string[][],
  handlers: MessageHandler[]
): CoupledFieldsResult {
  const violations: CoupledFieldsViolation[] = [];

  for (const rawGroup of coupledFields) {
    const group = rawGroup.map(norm);
    const groupSet = new Set(group);
    if (groupSet.size < 2) continue; // a group of <2 can have no strict subset

    for (const handler of handlers) {
      const violation = subsetViolation(group, groupSet, handler);
      if (violation) violations.push(violation);
    }
  }

  return { valid: violations.length === 0, violations };
}

/** Which of `group`'s (normalised) fields this handler assigns. */
function writtenFields(group: Set<string>, handler: MessageHandler): Set<string> {
  const written = new Set<string>();
  for (const assignment of handler.assignments) {
    const field = norm(assignment.field);
    if (group.has(field)) written.add(field);
  }
  return written;
}

/** A violation iff the handler wrote a NON-EMPTY STRICT subset of the group. */
function subsetViolation(
  group: string[],
  groupSet: Set<string>,
  handler: MessageHandler
): CoupledFieldsViolation | null {
  const written = writtenFields(groupSet, handler);
  if (written.size === 0 || written.size === groupSet.size) return null;
  return {
    group,
    handler: handler.messageType,
    written: group.filter((f) => written.has(f)),
    missing: group.filter((f) => !written.has(f)),
  };
}
