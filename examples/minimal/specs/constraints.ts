/**
 * Verification Constraints - Minimal Example
 *
 * Demonstrates state-level constraints in a separate file.
 * The analyzer discovers this file via transitive import following
 * from src/background/index.ts
 */

import { $constraints } from "@fairfox/polly/verify";

/**
 * Example constraint: PING requires user to be active
 *
 * This demonstrates:
 * - Constraints in specs/ directory (outside src/)
 * - Automatic discovery via import following
 * - Clean separation of verification from runtime code
 */
export const userConstraints = $constraints("user.active", {
  PING: {
    requires: "state.user.active === true",
    message: "User must be active to ping",
  },
});
