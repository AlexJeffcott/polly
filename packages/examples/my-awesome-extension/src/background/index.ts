/**
 * Background Service Worker
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";
import { MessageRouter } from "@fairfox/web-ext/message-router";

const bus = getMessageBus("background");
new MessageRouter(bus);

// Add your message handlers here
bus.on("PING", async () => {
  return { success: true, message: "pong" };
});

console.log("Background service worker initialized");
