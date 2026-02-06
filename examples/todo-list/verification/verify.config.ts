// Verification configuration for todo-list example
// Flagship example: exercises EVERY verification feature
import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    // User state
    "user.loggedIn": { type: "boolean" },
    "user.role": { type: "enum", values: ["guest", "user", "admin"] },
    "user.id": { values: ["guest", "user1", "user2", "user3"], abstract: false },
    "user.name": { values: ["Guest", "User1", "User2", "Admin"], abstract: false },

    // Todo state
    todos: { maxLength: 100 },
    filter: { type: "enum", values: ["all", "active", "completed"] },

    // Numeric state (exercises { type: "number" } verification — Issue #31)
    maxTodos: { type: "number", min: 1, max: 100 },

    // Priority enum (exercises parameter tracing for dynamic payload values)
    "todo.priority": { type: "enum", values: ["low", "medium", "high"] },
  },

  messages: {
    maxInFlight: 3,
    maxTabs: 2,
    tabSymmetry: true,

    // Per-message bounds (Tier 1 optimization)
    perMessageBounds: {
      USER_LOGIN: 1,
      USER_LOGOUT: 1,
      TODO_ADD: 2,
      TODO_SET_LIMIT: 1,
    },
  },

  // Tier 2 optimizations
  tier2: {
    temporalConstraints: [
      {
        before: "USER_LOGIN",
        after: "USER_LOGOUT",
        description: "Must login before logout",
      },
    ],
  },

  onBuild: "warn",
  onRelease: "error",
});
