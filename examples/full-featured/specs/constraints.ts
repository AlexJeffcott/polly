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

import { $constraints } from "@fairfox/polly/verify";

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
