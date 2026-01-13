# Formal Verification

This directory contains verification configuration for formally verifying the web extension framework using TLA+ model checking.

**Note:** For a complete, working example with verification, see `examples/todo-list/`.

## Overview

The verification system extracts message handlers from your codebase, analyzes their state transitions, and generates TLA+ specifications that can be model-checked with TLC to find concurrency bugs, race conditions, and invariant violations.

## Directory Structure

```
verification/
├── README.md              # This file
├── tsconfig.json          # TypeScript config for verification
├── verify.config.ts       # Verification configuration
├── verify.ts              # Verification script (run this!)
├── handlers-example.ts    # Example handlers with verification primitives
└── output/                # Generated TLA+ specs (gitignored)
    ├── UserApp.tla        # TLA+ specification
    └── UserApp.cfg        # TLC configuration
```

## Usage

### 1. Add Verification Primitives to Your Handlers

Use `requires()` and `ensures()` to specify preconditions and postconditions:

```typescript
import { requires, ensures } from '@verify/primitives'

messageBus.on("USER_LOGIN", (payload) => {
  // Preconditions - what must be true before
  requires(state.user.loggedIn === false, "User must not be logged in")
  requires(payload.userId !== null, "User ID must be provided")

  // State changes
  state.user.loggedIn = true
  state.user.id = payload.userId

  // Postconditions - what must be true after
  ensures(state.user.loggedIn === true, "User must be logged in")
  ensures(state.user.id === payload.userId, "User ID must match")
})
```

### 2. Configure Verification Bounds

Edit `verify.config.ts` to specify state bounds and verification settings:

```typescript
export const verificationConfig: VerificationConfig = {
  state: {
    'user.loggedIn': { type: 'boolean' },
    'user.role': { type: 'enum', values: ['guest', 'user', 'admin'] },
    'todoCount': { min: 0, max: 100 },
  },

  messages: {
    maxInFlight: 3,  // Max concurrent messages
    maxTabs: 1,      // Max tab IDs to verify
  },

  onBuild: 'warn',
  onRelease: 'error',
}
```

### 3. Generate TLA+ Specification

From the verification directory:

```bash
cd packages/polly/verification
bun verify.ts
```

This will:
1. Extract all message handlers
2. Parse verification primitives
3. Generate TLA+ specification in `output/UserApp.tla`
4. Generate TLC config in `output/UserApp.cfg`

### 4. Run Model Checker

With TLA+ Toolbox installed:

```bash
cd verification/output
tlc UserApp.tla -config UserApp.cfg
```

TLC will exhaustively explore all possible execution paths and report any violations of:
- Type safety
- Preconditions (requires)
- Postconditions (ensures)
- Message routing invariants

## Verification Primitives

### `requires(condition, message?)`

Specifies a precondition that must hold when the handler executes.

```typescript
requires(state.count < 100, "Cannot exceed limit")
```

### `ensures(condition, message?)`

Specifies a postcondition that must hold after the handler completes.

```typescript
ensures(state.count > 0, "Count must be positive")
```

### `invariant(name, condition)`

Specifies a global invariant that must always hold (not yet implemented).

```typescript
invariant("NonNegativeCount", () => state.count >= 0)
```

## Helper Functions

### `inRange(value, min, max)`

Checks if a value is within bounds:

```typescript
requires(inRange(state.count, 0, 100), "Count out of range")
```

### `oneOf(value, allowed)`

Checks if a value is in an allowed set:

```typescript
requires(oneOf(state.role, ['admin', 'user']), "Invalid role")
```

### `hasLength(array, constraint)`

Checks array length constraints:

```typescript
requires(hasLength(state.items, { max: 100 }), "Too many items")
```

## Tips

1. **Start Small** - Add verification to a few critical handlers first
2. **Use Examples** - See `handlers-example.ts` for patterns
3. **Iterate** - Run verification frequently during development
4. **Read Output** - TLC error traces show the exact sequence of events that leads to a violation
5. **Tune Bounds** - Reduce state space by carefully choosing bounds in `verify.config.ts`

## Common Issues

### "State space too large"

Reduce bounds in `verify.config.ts`:
- Lower `maxInFlight`
- Lower `maxTabs`
- Reduce enum/string value sets
- Use smaller numeric ranges

### "Postcondition violated"

The TLC trace will show:
1. Initial state
2. Sequence of messages
3. State after each message
4. The exact assertion that failed

Use this to debug your handler logic.

### "Deadlock detected"

All processes are waiting for each other. Check for:
- Missing message handlers
- Circular dependencies in message flows
- Incorrect port connection logic

## Next Steps

- Add verification primitives to critical handlers
- Run verification on pull requests
- Integrate with CI/CD
- Use TLC's simulation mode for faster feedback during development
