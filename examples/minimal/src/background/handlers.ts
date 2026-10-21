// Message handlers with verification primitives
import type { MessageBus } from "@fairfox/polly/message-bus";
import { $sharedState } from "@fairfox/polly/state";
import type { ExtensionMessage } from "@fairfox/polly/types";
import { ensures, requires } from "@fairfox/polly/verify";

// Define custom message types
type CustomMessages = { type: "PING" };

// Combined message type
export type AllMessages = ExtensionMessage | CustomMessages;

// Shared state - tracks whether user is active
export const user = $sharedState("user", { active: false });

/**
 * Register every handler on a bus.
 *
 * The background entry (index.ts) and the tests both call this against a bus
 * built by createBackground(), so the tests cross the same handler boundary
 * the extension does (polly#57).
 */
export function registerPingHandler(bus: MessageBus<AllMessages>): void {
  // Register a custom handler with verification primitives
  bus.on("PING", async () => {
    requires(user.value.active === true, "User must be active to ping");

    ensures(user.value.active === true, "User should remain active after ping");

    return { pong: true };
  });
}
