# Verification API

## Table of Contents
- [Overview](#overview)
- [requires / ensures](#requires--ensures)
- [$constraints](#constraints)
- [stateConstraint](#stateconstraint)
- [defineVerification](#defineverification)
- [State Config Types](#state-config-types)
- [Messages Config](#messages-config)
- [Tier 2 Optimizations](#tier-2-optimizations)
- [Complete Example](#complete-example)

## Overview

Polly's verification pipeline extracts runtime annotations into TLA+ specifications for model checking. The key insight: `requires()` and `ensures()` are **runtime no-ops** - they do nothing at runtime but are statically analyzed to generate TLA+ preconditions and postconditions.

Import everything from `@fairfox/polly/verify` (NOT the legacy `@fairfox/polly-verify`).

## requires / ensures

```typescript
import { requires, ensures } from '@fairfox/polly/verify'

bus.on('USER_LOGOUT', async () => {
  requires(loginState.value.loggedIn === true, 'Must be logged in to logout')

  loginState.value = { loggedIn: false }

  ensures(loginState.value.loggedIn === false, 'Must be logged out after logout')
  return { success: true }
})
```

**Rules:**
- Place `requires()` at the top of handlers (preconditions)
- Place `ensures()` after state mutations (postconditions)
- First arg is a boolean expression referencing verified state
- Second arg is a human-readable description
- Both are complete no-ops at runtime - zero performance cost

## $constraints

For complex state-dependent preconditions across multiple message types:

```typescript
import { $constraints } from '@fairfox/polly/verify'

$constraints('loginState', {
  USER_LOGOUT: {
    requires: 'loggedIn === true',           // String for TLA+
    message: 'Must be logged in to logout',
  },
  BOOKMARK_ADD: {
    requires: 'loggedIn === true',
    message: 'Must be logged in to add bookmarks',
  },
})
```

With optional runtime enforcement:

```typescript
$constraints('workspace', {
  TASK_CREATE: {
    requires: 'role !== "viewer"',
    predicate: (s) => s.role !== 'viewer',  // Runtime check
    message: 'Viewers cannot create tasks',
  },
}, { runtime: true })
```

## stateConstraint

Prunes structurally impossible states from the TLC exploration queue via the `CONSTRAINT` clause. Unlike `invariant()` (which checks but still explores) or `requires()` (which guards one action), `stateConstraint()` prevents TLC from ever reaching the pruned states.

```typescript
import { stateConstraint } from '@fairfox/polly/verify'

// Simple: expression body
stateConstraint("LeaderRequiresConnection", () =>
  !connectionState.value.isLeader || connectionState.value.status === "connected"
)

// With message
stateConstraint(
  "BookmarksRequireLogin",
  () => bookmarkCount.value <= 0 || loginState.value.loggedIn === true,
  { message: "Cannot have bookmarks without being logged in" },
)
```

**Signature:** `stateConstraint(name: string, predicate: () => boolean, options?: { message?: string }): void`

**Rules:**
- Runtime no-op (like `requires()`/`ensures()`)
- The predicate arrow function body is extracted as a string during static analysis
- Expression must use `signalName.value.field` or `state.field` references (same patterns as `requires()`)
- Translates to TLA+: `/\ \A ctx \in Contexts : (<translated expression>)` inside `StateConstraint ==`
- Place in a constraints file (e.g., `specs/constraints.ts`) imported from your main entry point
- For TypeScript to type-check state references in a separate file, use `declare const` for the signal variables

**When to use vs alternatives:**

| Primitive | TLA+ mapping | What it does |
|-----------|-------------|-------------|
| `requires()` | Guard on one handler action | Skips one action if condition is false |
| `invariant()` | `INVARIANT` clause | Checks condition in every state, still explores all states |
| `stateConstraint()` | `CONSTRAINT` clause | **Discards** states that violate the condition from the exploration queue |

Use `stateConstraint()` when fields are structurally correlated and exploring impossible combinations wastes time (e.g., "can't have bookmarks without being logged in").

## defineVerification

Modern config API. Place in `specs/verification.config.ts`:

```typescript
import { defineVerification } from '@fairfox/polly/verify'

export default defineVerification({
  state: { /* ... */ },
  messages: { /* ... */ },
  tier2: { /* ... */ },
  onBuild: 'warn',
  onRelease: 'error',
})
```

## State Config Types

```typescript
state: {
  // Boolean state
  loggedIn: { type: 'boolean' },
  // Legacy boolean (equivalent but less explicit)
  loggedIn: [false, true],

  // Numeric state with bounds (NEW - exercises TLA+ numeric comparisons)
  bookmarkCount: { type: 'number', min: 0, max: 20 },
  maxTodos: { type: 'number', min: 1, max: 100 },

  // Enum state
  priority: { type: 'enum', values: ['low', 'medium', 'high'] },

  // Array with length constraint
  todos: { maxLength: 50 },
}
```

**Important:** Field names in state config must match what the TLA+ analyzer generates from handler code. If a handler accesses `loginState.value.loggedIn`, the generated TLA+ field is `loginState_loggedIn`, NOT `loggedIn`. Use `[false, true]` style when the state variable name doesn't match (avoids field name mismatch errors).

## Messages Config

```typescript
messages: {
  maxInFlight: 2,        // Global concurrent message limit
  maxTabs: 1,            // Tab count for verification

  // Filter to only relevant message types (Tier 1 - zero precision loss)
  include: ['USER_LOGIN', 'USER_LOGOUT', 'BOOKMARK_ADD', 'SETTINGS_UPDATE'],

  // Per-message concurrency limits (Tier 1)
  perMessageBounds: {
    'USER_LOGIN': 1,       // Sequential
    'USER_LOGOUT': 1,      // Sequential
    'BOOKMARK_ADD': 2,     // Allow some concurrency
    'TAB_GET_CURRENT': 3,  // High concurrency OK
  },

  // Symmetry reduction (Tier 1)
  symmetry: [
    // Groups where order doesn't matter
    // ['worker1_msg', 'worker2_msg'],
  ],
}
```

## Tier 2 Optimizations

Minimal, controlled precision loss:

```typescript
tier2: {
  // Enforce ordering between message types
  temporalConstraints: [
    { before: 'USER_LOGIN', after: 'USER_LOGOUT', description: 'Must login before logout' },
    { before: 'USER_LOGIN', after: 'BOOKMARK_ADD', description: 'Must be logged in to bookmark' },
  ],

  // Limit state exploration depth
  boundedExploration: {
    maxDepth: 15,
  },
}
```

## Verification Engine Options

```typescript
verification?: {
  timeout?: number;   // Seconds before TLC is killed (0 = no limit, max 3600)
  workers?: number;   // TLC worker threads (1–16, default 1)
}
```

## Subsystem Config

```typescript
subsystems?: Record<string, {
  state: string[];      // Field names owned by this subsystem (from top-level state)
  handlers: string[];   // Message type names handled by this subsystem
}>
```

Rules:
- State fields must be partitioned (no field in multiple subsystems)
- Handlers must be partitioned (error if shared)
- Non-interference is checked automatically
- Unassigned handlers trigger warnings

## Complete Example

```typescript
// specs/verification.config.ts
import { defineVerification } from '@fairfox/polly/verify'

export default defineVerification({
  state: {
    loggedIn: [false, true],
    todoCount: { type: 'number', min: 0, max: 100 },
    priority: { type: 'enum', values: ['low', 'medium', 'high'] },
  },
  messages: {
    maxInFlight: 2,
    maxTabs: 1,
    include: ['USER_LOGIN', 'USER_LOGOUT', 'TODO_ADD', 'TODO_REMOVE', 'TODO_SET_LIMIT'],
    perMessageBounds: {
      'USER_LOGIN': 1,
      'USER_LOGOUT': 1,
      'TODO_ADD': 2,
      'TODO_SET_LIMIT': 1,
    },
  },
  tier2: {
    temporalConstraints: [
      { before: 'USER_LOGIN', after: 'USER_LOGOUT', description: 'Must login before logout' },
    ],
    boundedExploration: { maxDepth: 15 },
  },
  verification: {
    timeout: 300,
    workers: 2,
  },
  onBuild: 'warn',
  onRelease: 'error',
})
```
