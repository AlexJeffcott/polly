// Example configuration showcasing all Tier 1 & Tier 2 optimizations

import { defineVerification } from "@fairfox/polly/verify";

export default defineVerification({
  state: {
    // Field used by $constraints("loggedIn", { ... requires: "state.loggedIn === true" })
    loggedIn: [false, true],
    // Fields used by handler requires/ensures on loginState.value.loggedIn
    // (TLA+ generator flattens loginState.value.loggedIn → loginState_loggedIn)
    loginState_loggedIn: [false, true],
    loginState_username: { values: ['user1', 'user2'], abstract: true },
    // Verified numeric state for bookmark count (exercises { type: "number" })
    bookmarkCount: { type: "number", min: 0, max: 20 },
  },

  messages: {
    // Concurrent message handling (tests real-world scenarios)
    maxInFlight: 2,
    maxTabs: 1,

    // ═══════════════════════════════════════════════════════════
    // TIER 1 OPTIMIZATIONS (Zero precision loss)
    // ═══════════════════════════════════════════════════════════

    // 1. Message Type Filtering (Issue #12)
    // Reduces 43 message types → 7 message types (84% reduction!)
    include: [
      'USER_LOGIN',
      'USER_LOGOUT',
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
    // Limit depth to keep verification tractable. Lowered from 8 to 4
    // when deliveredTo was added to the message record (issue #75) —
    // recording the routed target makes routing nondeterminism
    // observable, which multiplies distinct states by a factor of
    // |targets| per delivered message. Pre-fix the example "passed"
    // at depth 8 only because the property false-positived on the
    // first multi-target send and TLC stopped early; post-fix the
    // spec is actually checked exhaustively, and depth 4 is what
    // completes within Docker's state-pool budget.
    boundedExploration: {
      maxDepth: 4,
    },
  },

  onBuild: 'warn',
  onRelease: 'error',
});
