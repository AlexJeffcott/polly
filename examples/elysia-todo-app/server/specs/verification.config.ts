// Verification configuration for Elysia Todo App
// Demonstrates Polly Verify for server-side apps via verified state discovery
import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: verification configs use default export by convention
export default defineVerification({
  state: {
    // Auth state (discovered via { verify: true } on $sharedState in state.ts)
    auth_loggedIn: { type: "boolean" },
    auth_userId: { values: ["user1", "user2"], abstract: true },

    // Todo count (exercises { type: "number" } verification)
    todoCount: { type: "number", min: 0, max: 100 },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },

  onBuild: "warn",
  onRelease: "error",
});
