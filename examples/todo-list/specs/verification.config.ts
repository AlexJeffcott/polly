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
  // Timeout for verification
  verification: {
    timeout: 900, // 15 minutes
    workers: 4, // Use 4 workers for parallel state exploration
  },

  // State bounds define the maximum complexity of state
  state: {
    // User state
    user: {
      // User can be logged in or not
      loggedIn: [true, false],
      // User roles
      role: ["guest", "user", "admin"],
    },

    // Todo list bounds
    todos: {
      // Maximum number of todos to model - keep at 2 for meaningful testing
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
    // Two concurrent messages tests race conditions
    maxInFlight: 2,

    // Maximum tab IDs (todo-list is tab-agnostic)
    maxTabs: 1,

    // Verify core operations: auth flow (LOGIN/LOGOUT) and CRUD (ADD/TOGGLE)
    exclude: ["GET_STATE", "GET_TODOS", "TODO_REMOVE", "TODO_CLEAR_COMPLETED"],
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
