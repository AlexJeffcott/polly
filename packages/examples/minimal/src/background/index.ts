// Background script - runs when extension loads
import { createBackground } from "@fairfox/web-ext/background";

const bus = createBackground();

// Register a custom handler
bus.on("PING", async () => ({ pong: true }));

console.log("Extension loaded!");
