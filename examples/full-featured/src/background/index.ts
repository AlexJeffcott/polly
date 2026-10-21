/**
 * Full-Featured Example - Background Script
 *
 * Demonstrates real-world extension patterns using the framework:
 * - State management with signals
 * - Chrome API usage through adapters
 * - Message routing between contexts
 * - Data persistence
 */

import { createBackground } from "@fairfox/polly/background";
// Import verification constraints (discovered via transitive import following)
import "../../specs/constraints.js";
import type { AllMessages } from "../shared/types/messages";
import { bookmarks, registerHandlers, settings } from "./handlers";

export { state } from "./handlers";

// The documented factory path: createBackground() wires the MessageBus +
// MessageRouter, then the shared helper registers the handlers.
const bus = createBackground<AllMessages>();
registerHandlers(bus);

// Initialize - wait for state to load from storage
// $sharedState automatically loads from storage in the background
// We only need to wait for completion if we need the loaded values immediately
(async () => {
  // Wait for state hydration to complete
  await settings.loaded;
  await bookmarks.loaded;

  console.log("[Full-Featured Extension] Background initialized");
})();
