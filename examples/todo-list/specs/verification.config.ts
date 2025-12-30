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
  // Use balanced preset (5 minutes timeout, 2 workers)
  preset: "balanced",

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
      maxLength: 3,

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
    // Maximum messages in flight simultaneously
    // Start with 2-3 for fast verification
    maxInFlight: 3,

    // Maximum tab IDs (todo-list is tab-agnostic)
    maxTabs: 1,
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
