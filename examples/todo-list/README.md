# Todo List Example

CRUD todo list with `requires()`/`ensures()` contracts and subsystem-scoped verification.

## What it demonstrates

- User authentication (login/logout) and todo CRUD
- Handler contracts checked exhaustively by TLC
- Subsystem-scoped verification: auth and todos verified independently
- `stateConstraint()` to prune impossible states
- Reactive `$sharedState` — popup stays in sync with no manual fetching

## Quick start

```bash
bun install
bun run build
```

Load in Chrome:
1. Go to `chrome://extensions`, enable Developer mode
2. Click "Load unpacked", select `dist/`
3. Click the extension icon

Run all checks (lint, typecheck, test, verify):

```bash
bun run test:all
```

## Handlers with contracts

Every handler declares what must be true before and after it runs:

```typescript
bus.on("TODO_ADD", (payload: { text: string }) => {
  requires(user.value.loggedIn === true, "Must be logged in");
  requires(todos.value.length < maxTodos.value, "Todo limit not reached");

  todos.value = [...todos.value, { id: generateId(), text: payload.text, completed: false }];

  ensures(todos.value.length > 0, "Todos must not be empty after add");
  return { success: true };
});
```

`requires()` and `ensures()` are runtime no-ops. `polly verify` reads them statically and generates a TLA+ specification that TLC model-checks across all message orderings and concurrent execution paths.

## Subsystem-scoped verification

The verification config splits the state space into independent subsystems:

```typescript
// specs/verification.config.ts
export const verificationConfig = defineVerification({
  state: { /* ... */ },
  messages: { maxInFlight: 2, maxTabs: 1 },
  subsystems: {
    auth: {
      state: ["user.loggedIn", "user.role"],
      handlers: ["USER_LOGIN", "USER_LOGOUT"],
    },
    todos: {
      state: ["todos"],
      handlers: ["TODO_ADD", "TODO_TOGGLE", "TODO_REMOVE", "TODO_CLEAR_COMPLETED"],
    },
  },
});
```

A non-interference check confirms the subsystems don't write to each other's state. Then TLC verifies each subsystem separately, keeping the state space small.

## File structure

```
src/
  background/
    handlers.ts             Message handlers with requires/ensures
    state.ts                $sharedState for user, todos, filter
    index.ts                Entry point
  popup/index.tsx           Preact UI
  shared/
    types.ts                Todo, User, AppState types
    messages.ts             Message type definitions
specs/
  verification.config.ts    Subsystem-scoped verification bounds
tests/
  handlers.test.ts          Unit tests
```

## Handlers

| Message | Preconditions | Effect |
|---------|--------------|--------|
| `USER_LOGIN` | Not logged in, valid userId | Sets loggedIn, role |
| `USER_LOGOUT` | Logged in | Resets to guest |
| `TODO_ADD` | Logged in, < 100 todos, non-empty text | Appends todo |
| `TODO_TOGGLE` | Todo exists | Flips completed |
| `TODO_REMOVE` | Todo exists | Removes todo |
| `TODO_CLEAR_COMPLETED` | — | Removes completed todos |

## Next steps

- [full-featured](../full-featured/) — production Chrome extension with `$constraints`, settings, bookmarks
- [elysia-todo-app](../elysia-todo-app/) — full-stack web app with Elysia + offline-first
