/**
 * Runtime constraint checking for message handlers
 *
 * Provides runtime enforcement of $constraints() declarations.
 * Constraints can be checked before handler execution to ensure preconditions are met.
 */

type ConstraintFunction = (state: any) => boolean;

type Constraint = {
  requires?: ConstraintFunction;
  ensures?: ConstraintFunction;
  message?: string;
};

// Registry maps: stateField -> messageType -> constraint
const registry = new Map<string, Map<string, Constraint>>();

/**
 * Register a constraint for runtime checking.
 *
 * @param field - State field this constraint applies to
 * @param messageType - Message type this constraint applies to
 * @param constraint - Constraint definition with requires/ensures predicates
 */
export function registerConstraint(field: string, messageType: string, constraint: Constraint): void {
  if (!registry.has(field)) {
    registry.set(field, new Map());
  }
  registry.get(field)!.set(messageType, constraint);
}

/**
 * Register multiple constraints for a state field.
 *
 * @param field - State field these constraints apply to
 * @param constraints - Map of messageType to constraint definitions
 */
export function registerConstraints(
  field: string,
  constraints: Record<string, {
    requires?: ConstraintFunction | string;
    ensures?: ConstraintFunction | string;
    message?: string;
  }>
): void {
  for (const [messageType, constraint] of Object.entries(constraints)) {
    // Only register function-based constraints (strings are for TLA+ generation)
    const runtimeConstraint: Constraint = {
      message: constraint.message,
    };

    if (typeof constraint.requires === 'function') {
      runtimeConstraint.requires = constraint.requires;
    }

    if (typeof constraint.ensures === 'function') {
      runtimeConstraint.ensures = constraint.ensures;
    }

    // Only register if there's at least one function-based constraint
    if (runtimeConstraint.requires || runtimeConstraint.ensures) {
      registerConstraint(field, messageType, runtimeConstraint);
    }
  }
}

/**
 * Check preconditions for a message type before handler execution.
 *
 * @param messageType - The message type being handled
 * @param state - Current state object to check against
 * @throws Error if any precondition fails
 */
export function checkPreconditions(messageType: string, state: any): void {
  for (const [field, constraints] of registry) {
    const constraint = constraints.get(messageType);
    if (constraint?.requires) {
      try {
        const result = constraint.requires(state);
        if (!result) {
          const message = constraint.message || `Precondition failed for ${messageType} on field ${field}`;
          throw new Error(message);
        }
      } catch (error) {
        // Re-throw with context if it's our error, otherwise wrap it
        if (error instanceof Error && error.message.includes('Precondition failed')) {
          throw error;
        }
        const message = constraint.message || `Precondition check error for ${messageType} on field ${field}`;
        throw new Error(`${message}: ${error}`);
      }
    }
  }
}

/**
 * Check postconditions for a message type after handler execution.
 *
 * @param messageType - The message type that was handled
 * @param state - Current state object to check against
 * @throws Error if any postcondition fails
 */
export function checkPostconditions(messageType: string, state: any): void {
  for (const [field, constraints] of registry) {
    const constraint = constraints.get(messageType);
    if (constraint?.ensures) {
      try {
        const result = constraint.ensures(state);
        if (!result) {
          const message = constraint.message || `Postcondition failed for ${messageType} on field ${field}`;
          throw new Error(message);
        }
      } catch (error) {
        // Re-throw with context if it's our error, otherwise wrap it
        if (error instanceof Error && error.message.includes('Postcondition failed')) {
          throw error;
        }
        const message = constraint.message || `Postcondition check error for ${messageType} on field ${field}`;
        throw new Error(`${message}: ${error}`);
      }
    }
  }
}

/**
 * Clear all registered constraints (useful for testing).
 */
export function clearConstraints(): void {
  registry.clear();
}

/**
 * Get all registered constraints (for debugging).
 */
export function getRegisteredConstraints(): Map<string, Map<string, Constraint>> {
  return new Map(registry);
}

/**
 * Check if runtime constraint checking is enabled.
 * Controlled via POLLY_RUNTIME_CONSTRAINTS environment variable.
 */
export function isRuntimeConstraintsEnabled(): boolean {
  // Check environment variable
  if (typeof process !== 'undefined' && process.env) {
    return process.env['POLLY_RUNTIME_CONSTRAINTS'] === 'true';
  }

  // Check for Bun
  if (typeof Bun !== 'undefined' && Bun.env) {
    return Bun.env['POLLY_RUNTIME_CONSTRAINTS'] === 'true';
  }

  // Default: disabled
  return false;
}
