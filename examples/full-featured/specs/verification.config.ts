// ═══════════════════════════════════════════════════════════════
// Verification Configuration for Full-Featured Extension
// ═══════════════════════════════════════════════════════════════
//
// This configuration defines bounds for TLA+ verification.
// It models authentication, bookmarks, settings, and tab operations.
//

import { defineVerification } from "@fairfox/polly/verify";

// biome-ignore lint/style/noDefaultExport: Config files require default exports
export default defineVerification({
  // State bounds define the maximum complexity of state
  state: {
    // User authentication
    user: {
      // User can be authenticated or not
      authenticated: [true, false],
    },

    // Bookmarks collection
    bookmarks: {
      // Maximum bookmarks to model
      // Keep small for fast verification
      maxLength: 2,

      item: {
        // Bookmarks don't have complex internal state
        // Just verify the collection operations
      },
    },

    // Settings state
    settings: {
      // Theme options
      theme: ["auto", "light", "dark"],

      // Boolean settings
      autoSync: [true, false],
      debugMode: [true, false],
      notifications: [true, false],

      // Numeric ranges
      refreshInterval: {
        min: 30000, // 30 seconds
        max: 300000, // 5 minutes
        step: 30000,
      },
    },

    // Active tab (for TAB_GET_CURRENT operations)
    activeTab: {
      exists: [true, false],
    },
  },

  // Message concurrency bounds
  messages: {
    // Maximum messages in flight simultaneously
    // Full-featured has more handlers, so keep this low
    maxInFlight: 2,

    // Tab operations (single tab should be sufficient)
    maxTabs: 1,
  },

  // Verification behavior
  onBuild: "warn", // Show warnings during development
  onDeploy: "error", // Block deployment on violations

  // Properties to verify
  properties: {
    // Safety: No duplicate bookmark IDs
    noDuplicateBookmarkIds: true,

    // Safety: Settings always have valid values
    settingsAlwaysValid: true,

    // Safety: Can't open tab without URL
    tabOpenRequiresUrl: true,

    // Liveness: User can eventually login
    canLogin: true,

    // Liveness: Bookmarks can be added/removed
    canManageBookmarks: true,

    // Liveness: Settings can be updated
    canUpdateSettings: true,

    // Consistency: Settings persist across operations
    settingsPersist: true,
  },
});
