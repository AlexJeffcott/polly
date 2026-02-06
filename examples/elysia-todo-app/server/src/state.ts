// Verified state declarations for TLA+ generation
import { $sharedState } from "@fairfox/polly/state";

// Authentication state (exercises { verify: true } for state discovery)
export const authState = $sharedState(
  "auth",
  { loggedIn: false, userId: null as string | null },
  { verify: true }
);

// Todo count (exercises { type: "number" } verification)
export const todoCount = $sharedState("todoCount", 0, { verify: true });
