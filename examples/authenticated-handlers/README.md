# Authenticated Handlers Example

This example demonstrates how to use function references with `bus.on()` for formal verification, allowing you to separate handler definitions from registration.

## Problem

When using `$constraints()` with `requires` clauses, the generated TLA+ handlers need to include precondition guards and state transitions. This requires extracting state mutations from handler functions.

## Solution

Define handler functions separately and use them with `bus.on()`:

```typescript
export function handleConnect() {
  state.connected = true;
  state.authenticated = false;
}

export function handleAuthenticate() {
  state.authenticated = true;
}

// Register handlers - extractor resolves function references
bus.on("connect", handleConnect);
bus.on("authenticate", handleAuthenticate);
```

The static analyzer will:
1. Discover handlers via `bus.on()` calls
2. Resolve function references (e.g., `handleQuery`)
3. Extract state transitions from function bodies
4. Wire `$constraints()` requires clauses as preconditions
5. Generate TLA+ handlers with guards and state updates

## Expected TLA+ Output

```tla
\* Handler for query
HandleQuery(ctx) ==
  /\ contextStates[ctx].authenticated = TRUE  \* Must authenticate before querying
  /\ contextStates[ctx].connected = TRUE      \* Must be connected to query
  /\ contextStates' = [contextStates EXCEPT
       ![ctx].pendingOperations = IF @ < 2 THEN @ + 1 ELSE @]

\* Handler for authenticate
HandleAuthenticate(ctx) ==
  /\ contextStates[ctx].connected = TRUE  \* Must be connected to authenticate
  /\ contextStates' = [contextStates EXCEPT
       ![ctx].authenticated = TRUE]

\* Handler for connect
HandleConnect(ctx) ==
  /\ contextStates' = [contextStates EXCEPT
       ![ctx].connected = TRUE,
       ![ctx].authenticated = FALSE,
       ![ctx].pendingOperations = 0]
```

## Key Features

1. **Precondition Guards**: The `$constraints()` requires clauses are automatically wired as preconditions in TLA+ handlers
2. **State Transitions**: State mutations from handler bodies are translated to TLA+ EXCEPT clauses
3. **Function References**: Handlers can be defined separately and referenced, improving code organization
4. **Standard Patterns**: Uses familiar `bus.on()` pattern - no new APIs to learn

## Verification

Run verification to generate TLA+ and check with TLC:

```bash
bun run polly verify examples/authenticated-handlers/specs/verification.config.ts
```

The model checker will verify that:
- Query messages cannot be delivered without authentication
- Authentication requires connection
- State transitions match the model
- Temporal constraints are satisfied
