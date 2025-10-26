// Background script - runs when extension loads
import { createBackground } from "@fairfox/polly/background";
import type { ExtensionMessage } from "@fairfox/polly/types";

// Define custom message types
type CustomMessages = { type: "PING" };

// Combined message type
type AllMessages = ExtensionMessage | CustomMessages;

const bus = createBackground<AllMessages>();

// Register a custom handler
bus.on("PING", async () => ({ pong: true }));

console.log("Extension loaded!");
