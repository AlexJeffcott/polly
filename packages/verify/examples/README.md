# Verification Examples

This directory contains examples demonstrating the adapter-based verification system.

## Overview

The verify package supports **any message-passing system** through a pluggable adapter architecture:

```
┌─────────────────────────────────────────────────────────────┐
│           User Configuration Layer                          │
│  (defines domain-specific messaging patterns)               │
└─────────────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────────┐
│        Routing Model Adapters (Pluggable)                   │
│  • WebExtension  • EventBus  • Worker  • Custom             │
└─────────────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────────┐
│         Core Verification Engine                            │
│  (domain-agnostic TLA+ generation & checking)               │
└─────────────────────────────────────────────────────────────┘
```

## Examples

### 1. Event Bus Example (`event-bus-example.ts`)

Demonstrates verification of an **event-driven application** using Node.js EventEmitter.

**Features:**
- User authentication state management
- Notification system with bounds checking
- Role-based access control
- Uses `requires()` and `ensures()` for verification

**Configuration:** `event-bus-verify.config.ts`

```typescript
import { EventBusAdapter } from '@fairfox/web-ext-verify'

const adapter = new EventBusAdapter({
  tsConfigPath: "./tsconfig.json",
  emitterLibrary: "events",
  maxInFlight: 5,
})

export default {
  adapter,
  state: {
    "user.loggedIn": { type: "boolean" },
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },
    "notifications.count": { min: 0, max: 10 },
  },
}
```

**Run the example:**
```bash
bun run examples/event-bus-example.ts
```

### 2. Web Extension Example

See the `packages/examples/todo-list/` directory for a complete Chrome extension example using the `WebExtensionAdapter`.

## Available Adapters

### WebExtensionAdapter

Verifies Chrome extensions with multiple contexts (background, content, popup, etc.).

```typescript
import { WebExtensionAdapter } from '@fairfox/web-ext-verify'

const adapter = new WebExtensionAdapter({
  tsConfigPath: "./tsconfig.json",
  contexts: ["background", "content", "popup"],
  maxTabs: 2,
  maxInFlight: 6,
})
```

**Recognizes:**
- Extension contexts (background, content, popup, devtools, options, offscreen, sidepanel)
- `bus.on(type, handler)` pattern for message handling
- Tab-based message routing
- Chrome extension APIs

### EventBusAdapter

Verifies event-driven systems using EventEmitter patterns.

```typescript
import { EventBusAdapter } from '@fairfox/web-ext-verify'

const adapter = new EventBusAdapter({
  tsConfigPath: "./tsconfig.json",
  emitterLibrary: "events", // or "mitt", "eventemitter3"
  maxInFlight: 5,
  maxEmitters: 3,
})
```

**Recognizes:**
- `emitter.on(event, handler)` pattern
- `emitter.emit(event, data)` pattern
- EventEmitter instances (Node.js, mitt, eventemitter3)
- Broadcast (one-to-many) routing

## Creating Custom Adapters

You can create custom adapters for your own messaging systems:

```typescript
import { RoutingAdapter, AdapterConfig } from '@fairfox/web-ext-verify'

export class MyCustomAdapter implements RoutingAdapter {
  readonly name = "my-custom-adapter"

  constructor(public readonly config: AdapterConfig) {
    // Initialize
  }

  extractModel(): CoreVerificationModel {
    // Extract nodes, messages, routing rules, handlers
  }

  recognizeMessageHandler(node: Node): MessageHandler | null {
    // Recognize your message handler pattern
  }

  recognizeStateUpdate(node: Node): StateAssignment | null {
    // Recognize state mutations
  }

  recognizeVerificationCondition(
    node: Node,
    type: "precondition" | "postcondition"
  ): VerificationCondition | null {
    // Recognize requires()/ensures() calls
  }
}
```

See `src/adapters/web-extension/` or `src/adapters/event-bus/` for complete examples.

## Verification Primitives

All adapters support these universal verification primitives:

### `requires(condition, message?)`

Assert a **precondition** that must hold when the handler executes.

```typescript
bus.on("USER_LOGIN", (payload) => {
  requires(state.user.loggedIn === false, "User must not be logged in")
  // ... handler logic
})
```

### `ensures(condition, message?)`

Assert a **postcondition** that must hold after the handler completes.

```typescript
bus.on("USER_LOGIN", (payload) => {
  state.user.loggedIn = true
  ensures(state.user.loggedIn === true, "User must be logged in")
})
```

### `invariant(name, condition)`

Define a **global invariant** that must always hold across all states.

```typescript
invariant("UserIdConsistent", () =>
  state.user.loggedIn === false || state.user.id !== null
)
```

## State Configuration

State configuration is **domain-agnostic** and works with all adapters:

```typescript
{
  state: {
    // Boolean fields (auto-configured)
    "user.loggedIn": { type: "boolean" },

    // Enums (provide all values)
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },

    // Numbers (provide min/max bounds)
    "counter": { min: 0, max: 100 },

    // Arrays (provide max length)
    "todos": { maxLength: 10 },

    // Strings (provide example values or use abstract)
    "username": { values: ["alice", "bob", "charlie"] },
    "userId": { abstract: true }, // Symbolic verification

    // Maps/Sets (provide max size)
    "cache": { maxSize: 5 },
  }
}
```

## Next Steps

1. **Try the examples**: Run `bun run examples/event-bus-example.ts`
2. **Read the design doc**: See `GENERALIZATION_DESIGN.md` for architecture details
3. **Create your adapter**: Implement `RoutingAdapter` for your messaging system
4. **Contribute**: Submit your adapter as a PR to help the community!

## Resources

- [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)
- [Formal Verification Guide](../docs/VERIFICATION.md) _(coming soon)_
- [Adapter Development Guide](../docs/ADAPTERS.md) _(coming soon)_
