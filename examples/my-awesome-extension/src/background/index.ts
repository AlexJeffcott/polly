/**
 * Background Service Worker
 */

import { getMessageBus } from "@fairfox/polly/message-bus";
import { MessageRouter } from "@fairfox/polly/message-router";
import type { ExtensionMessage } from "@fairfox/polly/types";

// Define custom message types
type CustomMessages = { type: "PING" };
type AllMessages = ExtensionMessage | CustomMessages;

const bus = getMessageBus<AllMessages>("background");
new MessageRouter(bus);

// Add your message handlers here
bus.on("PING", async () => {
  return { success: true, message: "pong" };
});

console.log("Background service worker initialized");
