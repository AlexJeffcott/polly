// Verification configuration for the web extension
import type { VerificationConfig } from "@fairfox/web-ext-verify";

export const verificationConfig: VerificationConfig = {
  preset: "balanced",

  state: {
    // User state
    "user.loggedIn": { type: "boolean" },
    "user.role": { type: "enum", values: ["guest", "user", "admin"] },
    "user.id": { values: ["guest", "user1", "user2", "user3"], abstract: false },

    // Todo state
    todoCount: { min: 0, max: 100 },
  },

  messages: {
    maxInFlight: 3,
    maxTabs: 1,
  },

  onBuild: "warn",
  onRelease: "error",
};
