// Example configuration showcasing all Tier 1 & Tier 2 optimizations

import { defineVerification } from "@fairfox/polly/verify";

export default defineVerification({
  state: {},

  messages: {
    maxInFlight: 3,
    maxTabs: 1,

    // ═══════════════════════════════════════════════════════════
    // TIER 1 OPTIMIZATIONS (Zero precision loss)
    // ═══════════════════════════════════════════════════════════

    // 1. Message Type Filtering (Issue #12)
    // Reduces 43 message types → 8 message types (81% reduction!)
    include: [
      'USER_LOGIN',
      'USER_LOGOUT',
      'USER_VERIFY',
      'BOOKMARK_ADD',
      'BOOKMARK_REMOVE',
      'SETTINGS_GET',
      'SETTINGS_UPDATE',
      'TAB_GET_CURRENT',
    ],

    // 2. Symmetry Reduction
    // Groups of message types where order doesn't affect properties
    // (swapping them in any state produces equivalent behavior)
    symmetry: [
      // Example: if you have multiple identical workers
      // ['worker1_msg', 'worker2_msg', 'worker3_msg'],
    ],

    // 3. Per-Message Bounds
    // Different maxInFlight per message type for realistic concurrency
    perMessageBounds: {
      'USER_LOGIN': 1,        // Authentication is sequential
      'USER_LOGOUT': 1,       // Logout is sequential
      'BOOKMARK_ADD': 2,      // Allow some bookmark concurrency
      'BOOKMARK_REMOVE': 2,   // Allow some bookmark concurrency
      'SETTINGS_UPDATE': 1,   // Settings updates should be sequential
      'TAB_GET_CURRENT': 3,   // Tab queries can be concurrent
    },
  },

  // ═══════════════════════════════════════════════════════════
  // TIER 2 OPTIMIZATIONS (Minimal, controlled precision loss)
  // ═══════════════════════════════════════════════════════════

  tier2: {
    // 1. Temporal Constraints
    // Enforce known ordering requirements between message types
    temporalConstraints: [
      {
        before: 'USER_LOGIN',
        after: 'USER_LOGOUT',
        description: 'Must login before logout'
      },
      {
        before: 'USER_LOGIN',
        after: 'BOOKMARK_ADD',
        description: 'Must be logged in to add bookmarks'
      },
      {
        before: 'USER_LOGIN',
        after: 'SETTINGS_UPDATE',
        description: 'Must be logged in to update settings'
      },
    ],

    // 2. Bounded Exploration
    // Limit depth while ensuring critical paths are covered
    boundedExploration: {
      maxDepth: 15,  // Limit state exploration depth
      // Critical paths to ensure are explored (future feature)
      // criticalPaths: [
      //   ['USER_LOGIN', 'BOOKMARK_ADD', 'USER_LOGOUT'],
      //   ['USER_LOGIN', 'SETTINGS_UPDATE', 'USER_LOGOUT'],
      // ],
    },
  },

  onBuild: 'warn',
  onRelease: 'error',
});
