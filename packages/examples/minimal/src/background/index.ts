// Background script - runs when extension loads
import { createBackground } from "@fairfox/polly/background";

const bus = createBackground();

// Register a custom handler
bus.on("PING", async () => ({ pong: true }));

console.log("Extension loaded!");
