// Minimal verification config for testing

import { defineVerification } from '../../src/index'

export default defineVerification({
  state: {
    // Just a few simple fields
    "user.loggedIn": { type: 'boolean' },
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },  // Added "guest"
  },

  messages: {
    maxInFlight: 2,  // Reduce from 3
    maxTabs: 1,
  },

  onBuild: 'warn',
  onRelease: 'error',
})
