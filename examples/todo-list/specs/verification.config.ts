// Verification configuration for todo-list example
// Flagship example: exercises EVERY verification feature
import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    // User state
    "user.loggedIn": { type: "boolean" },
    "user.role": { type: "enum", values: ["guest", "user", "admin"] },

    // Todo state — maxLength 1 keeps NDET sequence operations tractable
    todos: { maxLength: 1 },

    // User preferences — exercises payload-domain wiring (issue #72)
    theme: { type: "enum", values: ["light", "dark", "system"] },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,

    // Per-message bounds (Tier 1 optimization)
    perMessageBounds: {
      USER_LOGIN: 1,
      USER_LOGOUT: 1,
      TODO_ADD: 1,
      TODO_TOGGLE: 1,
      TODO_REMOVE: 1,
      TODO_CLEAR_COMPLETED: 1,
      SET_THEME: 1,
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
      {
        before: "TODO_ADD",
        after: "TODO_TOGGLE",
        description: "Must add before toggle",
      },
      {
        before: "TODO_ADD",
        after: "TODO_REMOVE",
        description: "Must add before remove",
      },
    ],
    boundedExploration: {
      maxDepth: 8,
    },
  },

  // Compositional verification: auth and todos are independent subsystems.
  // Non-interference guarantees soundness of separate verification.
  subsystems: {
    auth: {
      state: ["user.loggedIn", "user.role"],
      handlers: ["USER_LOGIN", "USER_LOGOUT"],
    },
    todos: {
      state: ["todos"],
      handlers: ["TODO_ADD", "TODO_TOGGLE", "TODO_REMOVE", "TODO_CLEAR_COMPLETED"],
    },
    preferences: {
      state: ["theme"],
      handlers: ["SET_THEME"],
    },
  },

  onBuild: "warn",
  onRelease: "error",
});
