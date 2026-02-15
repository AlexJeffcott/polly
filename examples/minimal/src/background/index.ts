// Background script - runs when extension loads
import { createBackground } from "@fairfox/polly/background";
import { $sharedState } from "@fairfox/polly/state";
import type { ExtensionMessage } from "@fairfox/polly/types";
import { ensures, requires } from "@fairfox/polly/verify";
// Import verification constraints from specs/ directory
import "../../specs/constraints.js";

// Define custom message types
type CustomMessages = { type: "PING" };

// Combined message type
type AllMessages = ExtensionMessage | CustomMessages;

// Shared state - tracks whether user is active
export const user = $sharedState("user", { active: false });

const bus = createBackground<AllMessages>();

// Register a custom handler with verification primitives
bus.on("PING", async () => {
  requires(user.value.active === true, "User must be active to ping");

  ensures(user.value.active === true, "User should remain active after ping");

  return { pong: true };
});

console.log("Extension loaded!");
