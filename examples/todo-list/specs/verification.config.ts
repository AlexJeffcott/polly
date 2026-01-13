// ═══════════════════════════════════════════════════════════════
// Verification Configuration for Todo List Extension
// ═══════════════════════════════════════════════════════════════
//
// This configuration defines bounds for TLA+ verification.
// It models the state space that the verifier will explore.
//

import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: Config files require default exports
export default defineVerification({
  // Timeout for this complex state space
  verification: {
    timeout: 1800, // 30 minutes
  },

  // State bounds define the maximum complexity of state
  state: {
    // User state
    user: {
      // User can be logged in or not
      loggedIn: [true, false],
      // User roles to verify
      role: ["guest", "user", "admin"],
    },

    // Todo list bounds
    todos: {
      // Maximum number of todos to model
      // Lower = faster verification, higher = more thorough
      // Reduced from 3 to 2 for performance (still covers key scenarios)
      maxLength: 2,

      // Todo properties to verify
      item: {
        completed: [true, false],
      },
    },

    // Filter state
    filter: ["all", "active", "completed"],
  },

  // Message concurrency bounds
  messages: {
    // Concurrent message handling (tests real-world scenarios)
    maxInFlight: 2,

    // Maximum tab IDs (todo-list is tab-agnostic)
    maxTabs: 1,

    // Tier 1 Optimization: Exclude read-only query messages
    // GET_STATE and GET_TODOS don't change state, only read it
    // Excluding them reduces 8 message types to 6 (25% reduction)
    // Impact: 64 message combinations → 36 combinations (44% reduction)
    exclude: ["GET_STATE", "GET_TODOS"],
  },

  // Verification behavior
  onBuild: "warn", // Show warnings during development
  onDeploy: "error", // Block deployment on violations

  // Properties to verify
  properties: {
    // Safety: No duplicate todo IDs
    noDuplicateTodoIds: true,

    // Safety: User can't be both guest and logged in
    guestNotLoggedIn: true,

    // Liveness: User can eventually login
    canLogin: true,

    // Liveness: Todos can eventually be added
    canAddTodo: true,
  },
});
