# @fairfox/web-ext-verify

Formal verification for web extension message routing using TLA+.

## Overview

This package automatically generates TLA+ specifications from your TypeScript types and verifies correctness properties about your extension's message routing and state management.

## Features

- **Type-driven verification** - Extracts types from TypeScript, generates TLA+ automatically
- **Comment-driven configuration** - Smart config generation with inline guidance
- **High-level primitives** - Express common patterns easily (before, requires, ensures, etc.)
- **Progressive enhancement** - Start simple, add detail as needed
- **Escape hatch** - Drop to raw TLA+ for complex properties

## Installation

```bash
bun add @fairfox/web-ext-verify
```

## Quick Start

### 1. Generate Configuration

```bash
bun verify --setup
```

This analyzes your codebase and generates `specs/verification.config.ts` with smart comments guiding you through configuration.

### 2. Review and Complete Configuration

Open `specs/verification.config.ts` and fill in values marked with `/* CONFIGURE */`:

```typescript
export default defineVerification({
  state: {
    // Auto-configured (high confidence)
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },

    // Needs your input (low confidence)
    todos: { maxLength: /* CONFIGURE */ null },
    "user.id": { values: /* CONFIGURE */ null },
  }
})
```

### 3. Validate Configuration

```bash
bun verify --validate
```

This checks for incomplete configuration and validates bounds.

### 4. Run Verification

```bash
bun verify
```

This generates TLA+ specs and runs the model checker.

## Configuration Guide

### State Field Types

The system handles different TypeScript types automatically:

**Boolean** - Auto-configured, no setup needed
```typescript
initialized: boolean
// → { type: 'boolean' }
```

**Enum** - Auto-configured from union types
```typescript
role: "admin" | "user" | "guest"
// → { type: "enum", values: ["admin", "user", "guest"] }
```

**Array** - Needs maximum length
```typescript
todos: Todo[]
// → { maxLength: 10 }  // You configure this
```

**Number** - Needs range
```typescript
counter: number
// → { min: 0, max: 100 }  // You configure this
```

**String** - Needs concrete values or abstract flag
```typescript
userId: string
// → { values: ["user1", "user2", "guest"] }
// OR
// → { abstract: true }
```

**Map/Set** - Needs maximum size
```typescript
cache: Map<string, Data>
// → { maxSize: 5 }
```

### Configuration Markers

Generated config uses special markers:

- `/* CONFIGURE */` - You must replace with a value
- `/* REVIEW */` - Auto-generated value, please verify
- `null` - Must be replaced with concrete value

### Example Configuration

```typescript
// specs/verification.config.ts
import { defineVerification } from '@fairfox/web-ext/verify'

export default defineVerification({
  state: {
    // Arrays
    todos: { maxLength: 10 },

    // Numbers
    counter: { min: 0, max: 100 },
    todoCount: { min: 0, max: 20 },

    // Strings
    "user.id": { values: ["alice", "bob", "guest"] },
    "user.username": { abstract: true },

    // Enums (auto-configured)
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },
    "settings.theme": { type: "enum", values: ["light", "dark"] },

    // Booleans (auto-configured)
    "user.loggedIn": { type: "boolean" },
    initialized: { type: "boolean" },

    // Maps
    cache: { maxSize: 5 },
  },

  messages: {
    maxInFlight: 6,
    maxTabs: 2,
  },

  onBuild: "warn",
  onRelease: "error",
})
```

## Verification Primitives

Define correctness properties using high-level primitives:

```typescript
// specs/invariants.ts
import { before, requires, ensures, never, eventually } from '@fairfox/web-ext/verify'

export const invariants = [
  // Temporal ordering
  before("USER_LOGIN", "SYNC_TODOS"),
  before("USER_LOGIN", ["SYNC_TODOS", "FETCH_DATA"]),

  // State preconditions
  requires("SYNC_TODOS", (state) => state.user.loggedIn === true),
  requires("FETCH_DATA", (state) => state.initialized),

  // State postconditions
  ensures("USER_LOGIN", (state) => state.user.loggedIn === true),
  ensures("CLEAR_TODOS", (state) => state.todos.length === 0),

  // Concurrency control
  never.concurrent(["SYNC_TODOS", "CLEAR_TODOS"]),

  // Liveness
  eventually.delivers("FETCH_DATA", { timeout: 5000 }),

  // Escape hatch: raw TLA+
  defineInvariant("TodoCountConsistent", {
    description: "Todo count matches actual todos",
    raw: `
      \\A ctx1, ctx2 \\in Contexts :
        (ports[ctx1] = "connected" /\\ ports[ctx2] = "connected") =>
          todoCount[ctx1] = todoCount[ctx2]
    `
  }),
]
```

## CLI Commands

```bash
# Generate configuration
bun verify --setup

# Validate configuration
bun verify --validate

# Run verification
bun verify

# Show help
bun verify --help
```

## Configuration Validation

The validator detects common issues:

- **Incomplete configuration** - `/* CONFIGURE */` markers not replaced
- **Null placeholders** - `null` values that need concrete values
- **Invalid bounds** - min > max, negative lengths, etc.
- **Unrealistic bounds** - Values that will slow verification significantly

## Workflow

### Development

```typescript
// web-ext.config.ts
export default {
  verification: {
    enabled: true,
    onBuild: "warn",      // Show warnings, don't fail
    onRelease: "error",   // Block releases on violations
  }
}
```

During development:
- Verification runs on build
- Shows warnings if violations found
- Doesn't block the build

### Release

During release builds:
- Verification runs with full bounds
- Blocks the build if violations found
- Ensures shipped code is verified

## Architecture

```
TypeScript Types
      ↓
  [Extractor]
      ↓
  Type Analysis
      ↓
  [Config Generator]
      ↓
verification.config.ts  ← User fills in
      ↓
  [Validator]
      ↓
  TLA+ Spec Generation
      ↓
  [TLC Model Checker]
      ↓
  Verification Results
```

## Current Status

**✅ Implemented:**
- Type extraction from TypeScript
- Config generation with smart comments
- Config validation
- CLI interface

**🚧 In Progress:**
- TLA+ spec generation from config
- Primitives → TLA+ translation
- TLC Docker integration

**📋 Planned:**
- Watch mode
- Interactive setup mode
- State mutation extraction from handlers
- Violation trace mapping back to TypeScript

## Contributing

This is part of the @fairfox/web-ext monorepo. See the main README for contribution guidelines.

## License

MIT
