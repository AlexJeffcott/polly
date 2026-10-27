// Background script - runs when extension loads
import { createBackground } from "@fairfox/polly/background";
// Import verification constraints from specs/ directory
import "../../specs/constraints.js";
import { type AllMessages, registerHandlers } from "./handlers";

export { user } from "./handlers";

// The documented factory path: createBackground() wires the MessageBus +
// MessageRouter, then the shared helper registers the handlers.
const bus = createBackground<AllMessages>();
registerHandlers(bus);

console.log("Extension loaded!");
