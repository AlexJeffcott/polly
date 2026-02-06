/**
 * Verification Constraints
 *
 * State-level constraints declared separately from runtime code.
 * These are automatically wired as preconditions to message handlers
 * during TLA+ generation.
 *
 * Benefits of separate file:
 * - Clear separation of verification concerns from runtime logic
 * - Easy to review all constraints in one place
 * - Can be maintained by verification experts
 * - Doesn't pollute runtime code with verification details
 */

import { $constraints, stateConstraint } from "@fairfox/polly/verify";

// Type declarations for state references used in stateConstraint() predicates.
// These are never called at runtime — the verification engine extracts the
// expression text from the AST and translates it to TLA+.
declare const bookmarkCount: { value: number };
declare const loginState: { value: { loggedIn: boolean; username?: string } };

/**
 * Global state constraint: bookmarks require login
 *
 * Prunes structurally impossible states from the model checker's
 * exploration queue. Unlike invariant() (which checks but still explores),
 * stateConstraint() discards states entirely, dramatically reducing
 * the state space for correlated fields.
 */
stateConstraint(
  "BookmarksRequireLogin",
  () => bookmarkCount.value <= 0 || loginState.value.loggedIn === true,
  { message: "Cannot have bookmarks without being logged in" },
);

/**
 * Authentication constraints
 *
 * Ensures users must be logged in before performing protected operations.
 */
export const authConstraints = $constraints("loggedIn", {
  USER_LOGOUT: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to logout",
  },
  BOOKMARK_ADD: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to add bookmarks",
  },
  SETTINGS_UPDATE: {
    requires: "state.loggedIn === true",
    message: "Must be logged in to update settings",
  },
});
