// Background script entry point
import { createBackground } from "@fairfox/polly/background";
import type { TodoMessages } from "../shared/messages";
import { registerTodoHandlers } from "./handlers";

// The documented factory path: createBackground() wires the MessageBus +
// MessageRouter, then the shared composite helper registers the handlers. The
// BDD world (features/steps.ts) calls the same registerTodoHandlers() against a
// createBackground(createMockAdapters()) bus, so both cross the same boundary.
const bus = createBackground<TodoMessages>();
registerTodoHandlers(bus);

console.log("Todo List Extension: Background script initialized");
