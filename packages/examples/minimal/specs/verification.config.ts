// ═══════════════════════════════════════════════════════════════
// Verification Configuration
// ═══════════════════════════════════════════════════════════════
//
// This file configures TLA+ verification for your extension.
// Some values are auto-configured, others need your input.
//
// Look for:
//   • /* CONFIGURE */ - Replace with your value
//   • /* REVIEW */ - Check the auto-generated value
//   • null - Must be replaced with a concrete value
//
// Run 'bun verify' to check for incomplete configuration.
// Run 'bun verify --setup' for interactive help.
//

import { defineVerification } from '@fairfox/polly/verify'

export default defineVerification({
  state: {
  },

  messages: {
    // Maximum messages in flight simultaneously across all contexts.
    // Higher = more realistic concurrency, but exponentially slower.
    //
    // Recommended values:
    //   • 2-3: Fast verification (< 10 seconds)
    //   • 4-6: Balanced (10-60 seconds)
    //   • 8+: Thorough but slow (minutes)
    //
    // WARNING: State space grows exponentially! Start small.
    maxInFlight: 3,

    // Maximum tab IDs to model (content scripts are per-tab).
    //
    // Recommended:
    //   • 0-1: Most extensions (single tab or tab-agnostic)
    //   • 2-3: Multi-tab coordination
    //
    // Start with 0 or 1 for faster verification.
    maxTabs: 1,
  },

  // Verification behavior
  // ─────────────────────
  //
  // onBuild: What to do during development builds
  //   • 'warn' - Show warnings but don't fail (recommended)
  //   • 'error' - Fail the build on violations
  //   • 'off' - Skip verification
  //
  onBuild: 'warn',

  // onRelease: What to do during production builds
  //   • 'error' - Fail the build on violations (recommended)
  //   • 'warn' - Show warnings but don't fail
  //   • 'off' - Skip verification
  //
  onRelease: 'error',
})