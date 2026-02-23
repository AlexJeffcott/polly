# Full-Featured Example

Production Chrome extension with all framework features: `$sharedState` with verification mirrors, `$constraints`, settings management, and bookmarks.

## What it demonstrates

- `$sharedState` with `{ verify: true }` for TLA+ state discovery
- `$constraints()` for handler-level preconditions
- `stateConstraint()` to prune impossible verification states
- Settings, bookmarks, login/logout, tab management
- Verification with temporal constraints and bounded exploration

## Quick start

```bash
bun install
bun run build
```

Load in Chrome:
1. Go to `chrome://extensions`, enable Developer mode
2. Click "Load unpacked", select `dist/`
3. Click the extension icon

Run all checks:

```bash
bun run test:all
```

## Key patterns

### Verified shared state

Passing `{ verify: true }` creates a plain object mirror that `polly verify` can discover:

```typescript
export const loginState = $sharedState("loginState", { loggedIn: false, username: null }, { verify: true });
export const bookmarkCount = $sharedState("bookmarkCount", 0, { verify: true });
```

### Handler contracts

```typescript
bus.on("BOOKMARK_ADD", async (payload: { url: string; title: string }) => {
  requires(loginState.value.loggedIn === true, "Must be logged in");

  bookmarks.value = [...bookmarks.value, { url: payload.url, title: payload.title }];
  bookmarkCount.value = bookmarks.value.length;

  ensures(bookmarkCount.value > 0, "Must have at least one bookmark");
});
```

### State constraints

```typescript
// specs/constraints.ts
stateConstraint("BookmarksRequireLogin", "state.loggedIn === true || state.bookmarkCount === 0");
```

This tells TLC to skip states where bookmarks exist but nobody is logged in — impossible at runtime, and pruning them speeds up verification.

## File structure

```
src/
  background/index.ts       All handlers: login, bookmarks, settings, tabs
  shared/types/messages.ts  Message type definitions
specs/
  verification.config.ts    Verification bounds with temporal constraints
  constraints.ts            $constraints and stateConstraint definitions
tests/                      Unit tests
docs/architecture.dsl       Structurizr architecture diagram
```

## Next steps

- [minimal](../minimal/) — stripped-down version to understand the basics
- [elysia-todo-app](../elysia-todo-app/) — full-stack web app with server-side Polly middleware
