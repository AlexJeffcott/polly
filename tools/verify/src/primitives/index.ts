// Verification primitives for formal verification
// These are runtime no-ops but extracted during verification

/**
 * Assert a precondition that must be true when the handler executes.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ assertion
 *
 * @example
 * messageBus.on("USER_LOGIN", (payload) => {
 *   requires(state.user.loggedIn === false, "User must not be logged in")
 *   state.user.loggedIn = true
 * })
 */
export function requires(condition: boolean, message?: string): void {
  // Runtime no-op - only used during verification
  // Condition and message are checked during static analysis only
  void condition;
  void message;
}

/**
 * Assert a postcondition that must be true after the handler completes.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ assertion
 *
 * @example
 * messageBus.on("USER_LOGIN", (payload) => {
 *   state.user.loggedIn = true
 *   ensures(state.user.loggedIn === true, "User must be logged in")
 * })
 */
export function ensures(condition: boolean, message?: string): void {
  // Runtime no-op - only used during verification
  // Condition and message are checked during static analysis only
  void condition;
  void message;
}

/**
 * Define a global invariant that must always hold.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLA+ invariant
 *
 * @example
 * invariant("UserIdConsistent", () =>
 *   state.user.loggedIn === false || state.user.id !== null
 * )
 */
export function invariant(_name: string, condition: () => boolean): void {
  // Runtime no-op - only used during verification
  // Name and condition are checked during static analysis only
  void condition;
}

/**
 * Assert that a value is within a valid range.
 *
 * @example
 * requires(inRange(todoCount, 0, 100), "Todo count must be 0-100")
 */
export function inRange(value: number, min: number, max: number): boolean {
  return value >= min && value <= max;
}

/**
 * Assert that a value is one of the allowed values.
 *
 * @example
 * requires(oneOf(state.user.role, ["admin", "user"]), "Role must be admin or user")
 */
export function oneOf<T>(value: T, allowed: T[]): boolean {
  return allowed.includes(value);
}

/**
 * Assert that an array has a specific length constraint.
 *
 * @example
 * requires(hasLength(state.todos, { max: 10 }), "Too many todos")
 */
export function hasLength(array: unknown[], constraint: { min?: number; max?: number }): boolean {
  if (constraint.min !== undefined && array.length < constraint.min) return false;
  if (constraint.max !== undefined && array.length > constraint.max) return false;
  return true;
}

/**
 * Declare state-level constraints for verification and optional runtime checking.
 * Maps message types to preconditions on state fields.
 *
 * The parser automatically wires these constraints to handlers during verification.
 * Optionally, constraints can be enforced at runtime by passing `{ runtime: true }`.
 *
 * @example
 * // Verification only (TLA+ generation)
 * const state = { loggedIn: false };
 *
 * $constraints("loggedIn", {
 *   USER_LOGOUT: { requires: "state.loggedIn === true", message: "Must be logged in" },
 *   BOOKMARK_ADD: { requires: "state.loggedIn === true", message: "Must be logged in" },
 * });
 *
 * @example
 * // Runtime enforcement (function predicates)
 * $constraints("loggedIn", {
 *   USER_LOGOUT: {
 *     requires: (state) => state.loggedIn === true,
 *     message: "Must be logged in to logout"
 *   },
 * }, { runtime: true });
 */
export function $constraints(
  stateField: string,
  constraints: Record<
    string,
    {
      requires?: string | ((state: unknown) => boolean);
      ensures?: string | ((state: unknown) => boolean);
      message?: string;
    }
  >,
  options?: { runtime?: boolean }
): void {
  // Register constraints for runtime checking if enabled
  if (options?.runtime) {
    // Import dynamically to avoid circular dependencies
    // This is safe because it only happens at runtime, not during static analysis
    // @ts-expect-error - Dynamic import path resolves correctly at runtime
    import("../../../src/shared/lib/constraints.js")
      .then(({ registerConstraints }) => {
        registerConstraints(stateField, constraints);
      })
      .catch(() => {
        // Silently ignore - constraints module may not be available during static analysis
      });
  }

  // For verification: Still a no-op at runtime
  // Parser extracts these and wires them to TLA+ handlers
}

/**
 * Declare a global state constraint that prunes structurally impossible states.
 *
 * In production: No-op (compiled away)
 * In verification: Translated to TLC CONSTRAINT clause, discarding states
 * that violate the predicate from the exploration queue entirely.
 *
 * Unlike `invariant()` (which checks but still explores), `stateConstraint()`
 * prevents the model checker from ever reaching the pruned states.
 *
 * @example
 * stateConstraint("LeaderRequiresConnection", () =>
 *   !connectionState.value.isLeader || connectionState.value.status === "connected"
 * )
 */
export function stateConstraint(
  name: string,
  predicate: () => boolean,
  options?: { message?: string }
): void {
  void name;
  void predicate;
  void options;
}

// Re-export for convenience
export const verify = {
  requires,
  ensures,
  invariant,
  inRange,
  oneOf,
  hasLength,
  $constraints,
  stateConstraint,
};
