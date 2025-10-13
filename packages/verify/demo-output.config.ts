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

import { defineVerification } from '@fairfox/web-ext/verify'

export default defineVerification({
  state: {
    // ────────────────────────────────────────────────────────────
    // user.id: string | null
    // ────────────────────────────────────────────────────────────
    // ⚠️  Manual configuration required
    //
    // Strings need concrete values for precise verification.
    // Provide 2-3 representative values from your app.
    //
    // Note: This field is nullable (can be null)
    //
    // Examples:
    //   ["user_abc123", "user_xyz789", "guest_000"]
    //   ["active", "inactive", "pending"]
    //
    // Alternative: Use abstract verification (less precise, faster)
    //   { abstract: true }
    //
    // Provide 2-3 example values: ["value1", "value2", "value3"]
    // Or use { abstract: true } for symbolic verification
    //
    // CONFIGURE: Fill in the value below
    //
    "user.id": { values: /* CONFIGURE */ null },

    // ────────────────────────────────────────────────────────────
    // user.username: string | null
    // ────────────────────────────────────────────────────────────
    // ⚠️  Manual configuration required
    //
    // Strings need concrete values for precise verification.
    // Provide 2-3 representative values from your app.
    //
    // Note: This field is nullable (can be null)
    //
    // Examples:
    //   ["user_abc123", "user_xyz789", "guest_000"]
    //   ["active", "inactive", "pending"]
    //
    // Alternative: Use abstract verification (less precise, faster)
    //   { abstract: true }
    //
    // Provide 2-3 example values: ["value1", "value2", "value3"]
    // Or use { abstract: true } for symbolic verification
    //
    // CONFIGURE: Fill in the value below
    //
    "user.username": { values: /* CONFIGURE */ null },

    // ────────────────────────────────────────────────────────────
    // user.role: "admin" | "user" | "guest"
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Enum with 3 values
    //
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },

    // ────────────────────────────────────────────────────────────
    // user.loggedIn: boolean
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Boolean type - auto-configured
    //
    "user.loggedIn": { type: 'boolean' },

    // ────────────────────────────────────────────────────────────
    // todos: object[]
    // ────────────────────────────────────────────────────────────
    // ⚠️  Manual configuration required
    //
    // This array has no bounds in your code. Choose a maximum
    // length for verification. Tradeoffs:
    //   • Small (3-5): Fast, catches basic bugs
    //   • Medium (10-15): Balanced, catches most bugs
    //   • Large (20+): Thorough, much slower
    //
    // Choose maxLength: 5 (fast), 10 (balanced), or 20 (thorough)
    //
    // CONFIGURE: Fill in the value below
    //
    "todos": { maxLength: /* CONFIGURE */ null },

    // ────────────────────────────────────────────────────────────
    // todoCount: number
    // ────────────────────────────────────────────────────────────
    // ⚠️  Manual configuration required
    //
    // Numbers need a range. Choose min and max values based on
    // realistic bounds in your application.
    //
    // Examples:
    //   { min: 0, max: 100 }  // Counter
    //   { min: 0, max: 999999 }  // Timestamp
    //
    // Provide min and max values based on your application logic
    //
    // CONFIGURE: Fill in the value below
    //
    "todoCount": { min: /* REVIEW */ /* CONFIGURE */, max: /* REVIEW */ /* CONFIGURE */ },

    // ────────────────────────────────────────────────────────────
    // initialized: boolean
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Boolean type - auto-configured
    //
    "initialized": { type: 'boolean' },

    // ────────────────────────────────────────────────────────────
    // syncing: boolean
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Boolean type - auto-configured
    //
    "syncing": { type: 'boolean' },

    // ────────────────────────────────────────────────────────────
    // settings.theme: "light" | "dark"
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Enum with 2 values
    //
    "settings.theme": { type: "enum", values: ["light", "dark"] },

    // ────────────────────────────────────────────────────────────
    // settings.notifications: boolean
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Boolean type - auto-configured
    //
    "settings.notifications": { type: 'boolean' },

    // ────────────────────────────────────────────────────────────
    // settings.autoSync: boolean
    // ────────────────────────────────────────────────────────────
    // ✓ Auto-configured from code analysis
    //   Boolean type - auto-configured
    //
    "settings.autoSync": { type: 'boolean' },

    // ────────────────────────────────────────────────────────────
    // cache: Map
    // ────────────────────────────────────────────────────────────
    // ⚠️  Manual configuration required
    //
    // map needs a maximum size. How many entries
    // do you need to model to catch bugs?
    //
    // Recommended: 3-5 for most cases
    //
    // Provide maxSize (recommended: 3-5)
    //
    // CONFIGURE: Fill in the value below
    //
    "cache": { maxSize: /* CONFIGURE */ null },
  },

  messages: {
    // Maximum messages in flight simultaneously across all contexts.
    // Higher = more realistic concurrency, slower verification.
    //
    // Recommended ranges:
    //   • Quick: 4-6 messages
    //   • Balanced: 8-10 messages
    //   • Thorough: 15+ messages
    //
    // CONFIGURE: Choose based on your verification goals
    maxInFlight: /* CONFIGURE */ 6,

    // Maximum tab IDs to model (content scripts are per-tab).
    //
    // Recommended:
    //   • 2-3 tabs for most cases
    //   • 1 tab for single-tab extensions
    //
    // CONFIGURE: How many tabs does your extension typically use?
    maxTabs: /* CONFIGURE */ 2,
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