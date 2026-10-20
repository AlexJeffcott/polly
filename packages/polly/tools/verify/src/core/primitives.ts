// Verification Primitives (Domain-Agnostic)
//
// These are runtime no-ops but extracted during verification.
// They work with ANY message-passing system, not just web extensions.

// `requires` / `ensures` live in ../primitives/index.ts: the copy
// @fairfox/polly/verify exports, and the one POLLY_CONTRACTS enforces.
import { ensures, requires } from "../primitives/index";

export { ensures, requires };

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
  if (!condition() && process.env["NODE_ENV"] === "development") {
    // Intentionally empty - verification happens at compile time
  }
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
  stateConstraint,
};
