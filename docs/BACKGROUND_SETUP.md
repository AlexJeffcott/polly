# Background script setup

In a background context, use `createBackground()` to wire the bus:

```typescript
// src/background/index.ts
import { createBackground } from "@fairfox/polly/background";

const bus = createBackground();

bus.on("MY_MESSAGE", async (payload) => {
  return { success: true };
});
```

## Why not `getMessageBus("background")`?

The background context needs two collaborators, not one. `MessageBus`
handles local message processing — registered handlers, request /
response correlation, port lifecycle. `MessageRouter` handles routing
between extension contexts — popup, content, devtools, options,
offscreen. The router owns the single `chrome.runtime.onMessage`
listener that fans incoming messages out to the bus.

Calling `getMessageBus("background")` directly returns a bus without a
router; messages from other contexts never reach your handlers.
Constructing both by hand registers two listeners against
`chrome.runtime.onMessage`, which causes every handler to fire twice
per message.

`createBackground()` is the assembly that gets both pieces right:

```typescript
export function createBackground(): MessageBus {
  // 1. Create MessageBus without its own chrome.runtime.onMessage listener
  const bus = getMessageBus("background", undefined, { skipListenerSetup: true });

  // 2. Create MessageRouter which owns the single listener
  new MessageRouter(bus);

  return bus;
}
```

## Framework guard rails

Three independent guards catch the configurations that produce
double-execution bugs.

### Singleton router

Constructing a second `MessageRouter` against the same context throws:

```typescript
const bus1 = createBackground(); // ok
const bus2 = createBackground(); // throws
```

The thrown error message:

```
MessageRouter already exists!

Only ONE MessageRouter can exist in the background context.
Multiple MessageRouter instances will cause handlers to execute multiple times.

Fix: Ensure createBackground() is only called once at application startup.
```

### Listener-count warning

If anything other than the router registers a
`chrome.runtime.onMessage` listener, the runtime adapter prints:

```
WARNING: 2 chrome.runtime.onMessage listeners registered!

Multiple listeners will cause message handlers to execute multiple times.
This is usually caused by:
  1. Creating both MessageBus and MessageRouter with separate listeners
  2. Calling createBackground() multiple times
  3. Calling getMessageBus("background") after createBackground()

Fix: In background scripts, use createBackground() ONCE at startup.
```

### Double-execution tracker

In development mode, the framework records each `messageId` it
dispatches and surfaces a runtime error if any handler fires twice for
the same message:

```
DOUBLE EXECUTION DETECTED

Handler "TODO_ADD" executed 2 times for message abc-123.

This indicates multiple chrome.runtime.onMessage listeners are registered.
Common causes:
  1. Both MessageBus and MessageRouter registered listeners
  2. createBackground() called multiple times
  3. Handler registered in multiple places

Fix: Ensure only ONE listener is registered. In background scripts,
use createBackground() instead of getMessageBus().
```

## Correct usage

```typescript
import { createBackground } from "@fairfox/polly/background";

const bus = createBackground();

bus.on("USER_LOGIN", handleLogin);
bus.on("DATA_SYNC", handleSync);
bus.on("SETTINGS_UPDATE", handleSettings);
```

The patterns the guards exist to catch — `getMessageBus("background")`
without a router, manual `new MessageRouter(bus)`, multiple
`createBackground()` calls — should be replaced wherever they appear.

## Testing

`MessageRouter` exposes a static reset hook for tests so the singleton
constraint does not break test isolation:

```typescript
import { test, beforeEach } from "bun:test";
import { MessageRouter } from "@fairfox/polly/background";
import { createBackground } from "@fairfox/polly/background";

beforeEach(() => {
  MessageRouter.resetInstance();
});

test("handler works correctly", async () => {
  const bus = createBackground();
  // ...
});
```

## Architecture

```
┌─────────────────────────────────────────────────┐
│        Background script (service worker)        │
├─────────────────────────────────────────────────┤
│                                                   │
│  createBackground()                               │
│         │                                         │
│         ├──> MessageBus (no listener)             │
│         │         │                               │
│         │         └──> user handlers              │
│         │                                         │
│         └──> MessageRouter (single listener)      │
│                   │                               │
│                   └──> chrome.runtime.onMessage   │
│                             │                     │
│                             v                     │
│                   route to MessageBus             │
│                             │                     │
│                             v                     │
│                   invoke user handlers            │
│                                                   │
└─────────────────────────────────────────────────┘
```
