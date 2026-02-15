// Non-interference checker for subsystem-scoped verification
//
// Validates that handlers in one subsystem do not write to state
// fields owned by another subsystem. This property makes
// compositional verification sound.

import type { MessageHandler } from "../types";

export type NonInterferenceViolation = {
  handler: string;
  subsystem: string;
  writesTo: string;
  ownedBy: string;
};

export type NonInterferenceResult = {
  valid: boolean;
  violations: NonInterferenceViolation[];
};

/**
 * Check non-interference between subsystems.
 *
 * For each pair of subsystems, verifies that no handler in subsystem A
 * writes to a state field owned by subsystem B.
 */
export function checkNonInterference(
  subsystems: Record<string, { state: string[]; handlers: string[] }>,
  handlers: MessageHandler[]
): NonInterferenceResult {
  const violations: NonInterferenceViolation[] = [];

  // Build field → owner map
  const fieldOwner = new Map<string, string>();
  for (const [name, sub] of Object.entries(subsystems)) {
    for (const field of sub.state) {
      fieldOwner.set(field, name);
    }
  }

  // Build handler → subsystem map
  const handlerSubsystem = new Map<string, string>();
  for (const [name, sub] of Object.entries(subsystems)) {
    for (const h of sub.handlers) {
      handlerSubsystem.set(h, name);
    }
  }

  // Check each handler's assignments against subsystem boundaries
  for (const handler of handlers) {
    const subsystemName = handlerSubsystem.get(handler.messageType);
    if (!subsystemName) continue; // handler not in any subsystem

    for (const assignment of handler.assignments) {
      const fieldName = assignment.field;
      const owner = fieldOwner.get(fieldName);

      // If the field is owned by a different subsystem, that's a violation
      if (owner && owner !== subsystemName) {
        violations.push({
          handler: handler.messageType,
          subsystem: subsystemName,
          writesTo: fieldName,
          ownedBy: owner,
        });
      }
    }
  }

  return {
    valid: violations.length === 0,
    violations,
  };
}
