# Background Script Setup

## Quick Start

In your background script, use `createBackground()` to initialize the message bus:

```typescript
// src/background/index.ts
import { createBackground } from '@fairfox/web-ext/background'

const bus = createBackground()

bus.on('MY_MESSAGE', async (payload) => {
  // Handle message
  return { success: true }
})
```

## ⚠️ Important: Use createBackground() Not getMessageBus()

**Always use `createBackground()` in background scripts**, not `getMessageBus('background')`.

### Why?

The background context requires special setup:
- **MessageBus** handles local message processing
- **MessageRouter** handles routing between extension contexts (popup, content, devtools, etc.)

If you use `getMessageBus('background')` directly, you'll set up MessageBus **without** MessageRouter, causing messages from other contexts to never reach your handlers.

If you try to manually create both, you'll get **double execution bugs** where handlers run twice for every message.

### What createBackground() Does

```typescript
export function createBackground(): MessageBus {
  // 1. Create MessageBus without its own chrome.runtime.onMessage listener
  const bus = getMessageBus("background", undefined, { skipListenerSetup: true });

  // 2. Create MessageRouter which sets up the single listener
  new MessageRouter(bus);

  // 3. Return the bus for registering handlers
  return bus;
}
```

## Framework Protection

The framework includes multiple layers of protection against misconfiguration:

### 1. Singleton MessageRouter

Only one MessageRouter can exist. Attempting to create a second throws an error:

```typescript
// This will throw an error:
const bus1 = createBackground()  // OK
const bus2 = createBackground()  // ERROR: MessageRouter already exists!
```

**Error message:**
```
🔴 MessageRouter already exists!

Only ONE MessageRouter can exist in the background context.
Multiple MessageRouter instances will cause handlers to execute multiple times.

Fix: Ensure createBackground() is only called once at application startup.
```

### 2. Listener Registration Warning

If multiple `chrome.runtime.onMessage` listeners are registered, you'll see a warning:

```
⚠️  WARNING: 2 chrome.runtime.onMessage listeners registered!

Multiple listeners will cause message handlers to execute multiple times.
This is usually caused by:
  1. Creating both MessageBus and MessageRouter with separate listeners
  2. Calling createBackground() multiple times
  3. Calling getMessageBus('background') after createBackground()

Fix: In background scripts, use createBackground() ONCE at startup.
```

### 3. Development-Mode Double Execution Detection

In development mode, the framework automatically detects if a handler executes multiple times for the same message:

```
🔴 DOUBLE EXECUTION DETECTED

Handler "TODO_ADD" executed 2 times for message abc-123.

This indicates multiple chrome.runtime.onMessage listeners are registered.
Common causes:
  1. Both MessageBus and MessageRouter registered listeners
  2. createBackground() called multiple times
  3. Handler registered in multiple places

Fix: Ensure only ONE listener is registered. In background scripts,
use createBackground() instead of getMessageBus().
```

## Best Practices

### ✅ Correct Usage

```typescript
// src/background/index.ts
import { createBackground } from '@fairfox/web-ext/background'

// Call once at startup
const bus = createBackground()

// Register all handlers
bus.on('USER_LOGIN', handleLogin)
bus.on('DATA_SYNC', handleSync)
bus.on('SETTINGS_UPDATE', handleSettings)
```

### ❌ Incorrect Usage

```typescript
// DON'T: Using getMessageBus directly
const bus = getMessageBus('background')  // Missing MessageRouter!

// DON'T: Creating MessageRouter separately
const bus = getMessageBus('background')
new MessageRouter(bus)  // This creates double listeners!

// DON'T: Calling createBackground multiple times
const bus1 = createBackground()  // OK
const bus2 = createBackground()  // ERROR!
```

## Testing

When testing background handlers, ensure you reset the MessageRouter singleton:

```typescript
import { test, expect, beforeEach } from 'bun:test'
import { MessageRouter } from '@fairfox/web-ext/background'

beforeEach(() => {
  // Reset singleton for each test
  MessageRouter.resetInstance()
})

test('handler works correctly', async () => {
  const bus = createBackground()
  // ... test your handlers
})
```

## Architecture

```
┌─────────────────────────────────────────────────┐
│         Background Script (Service Worker)       │
├─────────────────────────────────────────────────┤
│                                                   │
│  createBackground()                               │
│         │                                         │
│         ├──> MessageBus (no listener)            │
│         │         │                               │
│         │         └──> User Handlers              │
│         │                                         │
│         └──> MessageRouter (single listener)     │
│                   │                               │
│                   └──> chrome.runtime.onMessage   │
│                             │                     │
│                             ▼                     │
│                   Route to MessageBus             │
│                             │                     │
│                             ▼                     │
│                   Invoke User Handlers            │
│                                                   │
└─────────────────────────────────────────────────┘
```

## Summary

1. **Always** use `createBackground()` in background scripts
2. **Never** use `getMessageBus('background')` directly
3. Call `createBackground()` **once** at application startup
4. The framework will warn you if you misconfigure it
5. All configuration errors are caught in development mode
