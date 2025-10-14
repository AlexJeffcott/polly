// ═══════════════════════════════════════════════════════════════
// Verification Configuration for Event Bus Example
// ═══════════════════════════════════════════════════════════════
//
// This config demonstrates using the EventBusAdapter to verify
// an event-driven application.

import { EventBusAdapter } from "../src/adapters/event-bus"

// ─────────────────────────────────────────────────────────────────
// Adapter Configuration
// ─────────────────────────────────────────────────────────────────

const adapter = new EventBusAdapter({
  tsConfigPath: "../tsconfig.json",
  emitterLibrary: "events", // Node.js EventEmitter
  maxInFlight: 5, // Max 5 concurrent events
  maxEmitters: 3, // Model up to 3 emitter instances
})

// ─────────────────────────────────────────────────────────────────
// Verification Configuration
// ─────────────────────────────────────────────────────────────────

export const config = {
  // The adapter to use
  adapter,

  // State bounds (same format as web extension config)
  state: {
    "user.loggedIn": { type: "boolean" },
    "user.username": { values: ["alice", "bob", null], abstract: false },
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },
    "notifications.count": { min: 0, max: 10 },
    "notifications.messages": { maxLength: 10 },
  },

  // Concurrency bounds
  bounds: {
    maxInFlight: 5,
  },

  // Verification behavior
  onBuild: "warn" as const,
  onRelease: "error" as const,
}

export default config
