// Verification configuration for todo-list example
import type { VerificationConfig } from '@fairfox/polly-verify'

export const verificationConfig: VerificationConfig = {
  preset: 'balanced',

  state: {
    // User state
    'user.loggedIn': { type: 'boolean' },
    'user.role': { type: 'enum', values: ['guest', 'user', 'admin'] },
    'user.id': { values: ['guest', 'user1', 'user2', 'user3'], abstract: false },
    'user.name': { values: ['Guest', 'User1', 'User2', 'Admin'], abstract: false },

    // Todo state
    'todos': { maxLength: 100 },
    'filter': { type: 'enum', values: ['all', 'active', 'completed'] },
  },

  messages: {
    maxInFlight: 3,  // Test with up to 3 concurrent messages
    maxTabs: 1,      // Single tab for simplicity
  },

  onBuild: 'warn',
  onRelease: 'error',
}
