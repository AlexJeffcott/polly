// Example completed verification config

import { defineVerification } from '../src/index'

export default defineVerification({
  state: {
    // Strings (nullable)
    "user.id": { values: ["user_123", "user_456", "guest"] },
    "user.username": { values: ["alice", "bob", "guest_user"] },

    // Enums (auto-configured)
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },

    // Booleans (auto-configured)
    "user.loggedIn": { type: 'boolean' },
    initialized: { type: 'boolean' },
    syncing: { type: 'boolean' },
    "settings.notifications": { type: 'boolean' },
    "settings.autoSync": { type: 'boolean' },

    // Arrays
    todos: { maxLength: 5 },

    // Numbers
    todoCount: { min: 0, max: 10 },

    // Enums (auto-configured)
    "settings.theme": { type: "enum", values: ["light", "dark"] },

    // Maps
    cache: { maxSize: 3 },
  },

  messages: {
    maxInFlight: 3,
    maxTabs: 1,
  },

  onBuild: 'warn',
  onRelease: 'error',
})
