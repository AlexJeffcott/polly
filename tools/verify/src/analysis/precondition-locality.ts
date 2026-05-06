// Precondition-locality checker for subsystem-scoped verification
//
// Validates that handlers in one subsystem do not read state fields
// owned by another subsystem in their `requires()` clauses. This is the
// read-side complement to non-interference: non-interference proves that
// compositional verification is sound on writes; precondition locality
// proves it is sound on reads.
//
// A handler in subsystem A whose `requires()` reads state owned by
// subsystem B will silently never have its postcondition evaluated
// under the compositional verification of A alone. None of B's handlers
// run during A's pass, so the pre-state A's handler waits for is never
// produced; from inside A's verification this looks identical to a
// handler that is unreachable, and TLC reports A as PASS without ever
// firing the property the user wrote.

import type { MessageHandler, VerificationCondition } from "../types";
import { extractFieldRefs } from "./expression-validator";

export type PreconditionLocalityViolation = {
  handler: string;
  subsystem: string;
  readsFrom: string;
  ownedBy: string;
  expression: string;
  location: { file: string; line: number; column: number };
};

export type PreconditionLocalityResult = {
  valid: boolean;
  violations: PreconditionLocalityViolation[];
};

/**
 * Resolve which subsystem owns a given field reference.
 *
 * Tries the ref as-is, with dots-to-underscores, and underscores-to-dots,
 * since `state` config keys are sometimes declared in either form. If the
 * ref ends with `.length` and no direct match is found, strip the suffix
 * and try again — `requires(todos.value.length > 0)` extracts `todos.length`
 * whose owner is the parent `todos` field.
 */
function findOwner(fieldRef: string, fieldOwner: Map<string, string>): string | undefined {
  const candidates = [fieldRef, fieldRef.replace(/\./g, "_"), fieldRef.replace(/_/g, ".")];
  for (const c of candidates) {
    const owner = fieldOwner.get(c);
    if (owner) return owner;
  }
  if (fieldRef.endsWith(".length")) {
    return findOwner(fieldRef.slice(0, -".length".length), fieldOwner);
  }
  return undefined;
}

function buildFieldOwner(subsystems: Record<string, { state: string[] }>): Map<string, string> {
  const fieldOwner = new Map<string, string>();
  for (const [name, sub] of Object.entries(subsystems)) {
    for (const field of sub.state) {
      fieldOwner.set(field, name);
    }
  }
  return fieldOwner;
}

function buildHandlerSubsystem(
  subsystems: Record<string, { handlers: string[] }>
): Map<string, string> {
  const handlerSubsystem = new Map<string, string>();
  for (const [name, sub] of Object.entries(subsystems)) {
    for (const h of sub.handlers) {
      handlerSubsystem.set(h, name);
    }
  }
  return handlerSubsystem;
}

function violationsForPrecondition(
  handler: MessageHandler,
  subsystemName: string,
  precondition: VerificationCondition,
  fieldOwner: Map<string, string>
): PreconditionLocalityViolation[] {
  const out: PreconditionLocalityViolation[] = [];
  for (const ref of extractFieldRefs(precondition.expression)) {
    const owner = findOwner(ref, fieldOwner);
    if (!owner || owner === subsystemName) continue;
    out.push({
      handler: handler.messageType,
      subsystem: subsystemName,
      readsFrom: ref,
      ownedBy: owner,
      expression: precondition.expression,
      location: {
        file: handler.location?.file ?? "",
        line: precondition.location?.line ?? 0,
        column: precondition.location?.column ?? 0,
      },
    });
  }
  return out;
}

/**
 * Check precondition locality between subsystems.
 *
 * For each handler's `requires()` expressions, collect the state fields
 * each precondition reads and flag any field owned by a subsystem other
 * than the handler's own. Reads of unowned fields and payload-only
 * preconditions are ignored — they cannot cross a subsystem boundary
 * and so cannot threaten the soundness of the decomposition.
 */
export function checkPreconditionLocality(
  subsystems: Record<string, { state: string[]; handlers: string[] }>,
  handlers: MessageHandler[]
): PreconditionLocalityResult {
  const fieldOwner = buildFieldOwner(subsystems);
  const handlerSubsystem = buildHandlerSubsystem(subsystems);

  const violations: PreconditionLocalityViolation[] = [];
  for (const handler of handlers) {
    const subsystemName = handlerSubsystem.get(handler.messageType);
    if (!subsystemName) continue;
    for (const precondition of handler.preconditions ?? []) {
      violations.push(
        ...violationsForPrecondition(handler, subsystemName, precondition, fieldOwner)
      );
    }
  }

  return { valid: violations.length === 0, violations };
}
