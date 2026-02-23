# Minimal Example

Counter with `$sharedState` — the simplest possible Polly app.

## What it demonstrates

- `$sharedState` for reactive, synced, persisted state
- `requires()` / `ensures()` on a handler
- TLA+ verification via `polly verify`
- Preact popup UI that re-renders automatically

Three source files, ~30 lines of code.

## Quick start

```bash
bun install
bun run build
```

Load in Chrome:
1. Go to `chrome://extensions`, enable Developer mode
2. Click "Load unpacked", select `dist/`
3. Click the extension icon

## How it works

Define state once:

```typescript
// src/shared/state.ts
import { $sharedState } from "@fairfox/polly/state";

export const counter = $sharedState("counter", 0);
```

Use it in the popup — the UI re-renders when `counter.value` changes:

```typescript
// src/popup/index.tsx
import { counter } from "../shared/state";

function Popup() {
  return (
    <div>
      <p>Count: {counter.value}</p>
      <button onClick={() => counter.value++}>Increment</button>
    </div>
  );
}
```

The background script adds a handler with verification contracts:

```typescript
// src/background/index.ts
bus.on("PING", () => {
  requires(user.value.active === true, "User must be active");
  // ...
  ensures(user.value.active === true, "User must still be active");
});
```

Run `bun run verify` to model-check all handler contracts with TLC.

## File structure

```
src/
  background/index.ts     Background service worker
  popup/index.tsx          Preact UI
  popup/popup.html         HTML template
  shared/state.ts          Shared reactive state
specs/
  verification.config.ts   TLA+ verification bounds
  constraints.ts           State constraints
tests/
  handlers.test.ts         Unit tests
```

## Next steps

- [todo-list](../todo-list/) — CRUD with subsystem-scoped verification
- [full-featured](../full-featured/) — production Chrome extension with all features
