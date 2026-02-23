// Verification configuration for Elysia Todo App
// Demonstrates Polly Verify for server-side apps via verified state discovery
import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: verification configs use default export by convention
export default defineVerification({
  state: {
    // Auth state — field names must match what handler extraction generates
    // from authState.value.loggedIn / authState.value.userId
    authState_loggedIn: { type: "boolean" },
    authState_userId: { values: ["user1", "user2"], abstract: true, nullable: true },

    // Todo count (exercises { type: "number" } verification)
    todoCount: { type: "number", min: 0, max: 100 },

    // $resource async lifecycle fields (todos resource)
    // These model the client-side fetch lifecycle for TLA+ verification.
    // The three synthetic handlers (todos_FetchStart/Success/Error) are
    // auto-discovered when $resource is in the analyzed tsconfig scope.
    todos_status: { type: "enum", values: ["idle", "loading", "success", "error"] },
    todos_error: { type: "boolean" },
  },

  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },

  onBuild: "warn",
  onRelease: "error",
});
