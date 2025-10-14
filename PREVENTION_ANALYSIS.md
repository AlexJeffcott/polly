# Systematic Prevention of Double-Handler Execution

## Problem Analysis

**What Happened:**
- MessageBus registered `chrome.runtime.onMessage` listener
- MessageRouter also registered `chrome.runtime.onMessage` listener
- Both fired for every message → handlers executed twice
- Tests didn't catch it (only tested handlers directly, not message infrastructure)
- Verification didn't catch it (no primitive for "executed exactly once")
- Manual review missed it (architectural issue not visible in handler code)

## Why Current Approaches Failed

### 1. Unit Tests Failed
**Why:** Tests called handlers directly, bypassing the message infrastructure
```typescript
// This test doesn't exercise chrome.runtime.onMessage at all
test('adding a todo', () => {
  state.todos.push(newTodo)  // Direct state manipulation
  expect(state.todos.length).toBe(1)
})
```

### 2. Verification Primitives Failed
**Why:** `ensures()` only checks postconditions, not "how many times did this run"
```typescript
ensures(state.todos.length === previousCount + 1, 'Todo count must increase by 1')
// ✓ Passes even with double execution: 0 + 1 + 1 = 2, which equals previousCount + 1... wait no
// Actually this SHOULD have failed! Let me check...
```

Wait, let me trace through what actually happens:
1. First handler invocation: previousCount = 0, adds todo, state.todos.length = 1, ensures(1 === 0 + 1) ✓
2. Second handler invocation: previousCount = 1 (reads current state!), adds todo, state.todos.length = 2, ensures(2 === 1 + 1) ✓

Ah! The verification WOULD catch it IF the handler read `previousCount` before both invocations. But since each invocation reads it fresh, each sees different values.

### 3. Integration Tests Failed
**Why:** No integration tests that actually exercise the full message passing flow

## Systematic Prevention Strategies

### Strategy 1: Runtime Handler Execution Tracking (HIGHEST PRIORITY)

Add a development-mode tracker that ensures each handler executes exactly once per message ID:

```typescript
class HandlerExecutionTracker {
  private executions = new Map<string, Map<string, number>>() // messageId → handlerName → count

  track(messageId: string, handlerType: string): void {
    if (process.env.NODE_ENV !== 'development') return

    if (!this.executions.has(messageId)) {
      this.executions.set(messageId, new Map())
    }

    const handlerCounts = this.executions.get(messageId)!
    const count = (handlerCounts.get(handlerType) || 0) + 1
    handlerCounts.set(handlerType, count)

    if (count > 1) {
      const error = new Error(
        `Handler "${handlerType}" executed ${count} times for message ${messageId}. ` +
        `This indicates multiple listeners are registered. Check for duplicate ` +
        `chrome.runtime.onMessage listeners.`
      )
      console.error(error)
      throw error
    }

    // Cleanup old messages
    setTimeout(() => this.executions.delete(messageId), 5000)
  }
}

// Usage in MessageBus.handleMessage:
public async handleMessage(message: RoutedMessage | RoutedResponse): Promise<unknown> {
  if (!("success" in message)) {
    // Before invoking handler
    this.executionTracker.track(message.id, message.payload.type)

    // Invoke handlers...
  }
}
```

**Pros:**
- Catches the exact bug we encountered
- Works in development, no runtime cost in production
- Clear error message points to root cause

**Cons:**
- Only works in development mode
- Requires message IDs (which we have)

### Strategy 2: Architectural Fix - Single Listener Ownership

**Current (BROKEN):**
- MessageBus owns a listener
- MessageRouter owns a listener
- Both active simultaneously

**Proposed:**
- Only MessageRouter registers chrome.runtime.onMessage
- MessageBus has NO listener when used with MessageRouter
- Pass a flag to MessageBus constructor: `skipListenerSetup: boolean`

```typescript
export function createBackground(): MessageBus {
  const bus = getMessageBus("background", undefined, { skipListenerSetup: true })
  new MessageRouter(bus)
  return bus
}

constructor(context: Context, adapters?: ExtensionAdapters, options?: { skipListenerSetup?: boolean }) {
  this.context = context;
  this.adapters = adapters || createChromeAdapters(context);
  this.errorHandler = new ErrorHandler(this.adapters.logger);
  this.helpers = this.createContextHelpers();

  if (!options?.skipListenerSetup) {
    this.setupListeners();
  }
}
```

**Pros:**
- Prevents the architectural issue by design
- Clear ownership model
- No runtime overhead

**Cons:**
- API change (though backwards compatible with defaults)
- Requires all background scripts use createBackground()

### Strategy 3: Listener Registration Detection

Detect when multiple listeners are registered:

```typescript
class ListenerRegistry {
  private static messageListenerCount = 0

  static increment(context: Context): void {
    this.messageListenerCount++

    if (context === 'background' && this.messageListenerCount > 1) {
      console.error(
        `WARNING: ${this.messageListenerCount} chrome.runtime.onMessage listeners ` +
        `registered in background context. This will cause handlers to execute ` +
        `multiple times. Use createBackground() instead of getMessageBus().`
      )
    }
  }

  static decrement(): void {
    this.messageListenerCount--
  }
}

// In setupListeners:
private setupListeners(): void {
  ListenerRegistry.increment(this.context)
  // ... rest of setup
}
```

**Pros:**
- Warns developers immediately
- Easy to implement

**Cons:**
- Only a warning, doesn't prevent the issue
- Not foolproof (external code could register listeners too)

### Strategy 4: Verification Primitive - Single Execution

Add a verification primitive specifically for handler execution:

```typescript
// In handler:
bus.on('TODO_ADD', (payload) => {
  mark_execution_start('TODO_ADD')  // Verification primitive

  requires(state.todos.length < 100)
  const previousCount = state.todos.length

  state.todos.push(newTodo)

  ensures(state.todos.length === previousCount + 1)
  mark_execution_end('TODO_ADD')  // Verification primitive
})

// Verification extracts this to TLA+:
// Check that between any two mark_execution_start('TODO_ADD') calls,
// there must be exactly one state change
```

**Pros:**
- Works with formal verification tooling
- Catches the issue at verification time

**Cons:**
- Requires verification to be run (not automatic)
- Complex to implement in TLA+
- Requires developer to add marks

### Strategy 5: Integration Tests with Real Chrome APIs

Create tests that actually exercise chrome.runtime.onMessage:

```typescript
// tests/integration/message-flow.test.ts
import { test, expect } from 'bun:test'

test('handler executes exactly once per message', async () => {
  // Mock chrome.runtime.onMessage
  const listeners: Function[] = []
  global.chrome = {
    runtime: {
      onMessage: {
        addListener: (fn: Function) => listeners.push(fn)
      },
      sendMessage: (msg: any) => {
        // Simulate Chrome calling all registered listeners
        listeners.forEach(listener => {
          listener(msg, {}, () => {})
        })
      }
    }
  }

  let executionCount = 0

  // Setup background (this should NOT double-register)
  const bus = createBackground()
  bus.on('TEST_MESSAGE', () => {
    executionCount++
    return { success: true }
  })

  // Send message
  chrome.runtime.sendMessage({ type: 'TEST_MESSAGE' })

  // Wait for async handling
  await new Promise(resolve => setTimeout(resolve, 10))

  // Assert handler ran exactly once
  expect(executionCount).toBe(1)
  expect(listeners.length).toBe(1)  // Only one listener registered
})
```

**Pros:**
- Would have caught this exact bug
- Tests real behavior, not implementation

**Cons:**
- Requires mocking chrome APIs
- More complex test setup

### Strategy 6: State Invariant - Idempotency Violation Detection

Add framework-level verification that state changes are consistent with single execution:

```typescript
class StateChangeTracker {
  private beforeState: any
  private expectedDelta: any

  recordPrecondition(handler: string, key: string, currentValue: any, expectedDelta: number) {
    this.beforeState = { handler, key, value: currentValue }
    this.expectedDelta = expectedDelta
  }

  verifyPostcondition(key: string, currentValue: any) {
    if (!this.beforeState) return

    const actualDelta = currentValue - this.beforeState.value

    if (actualDelta !== this.expectedDelta) {
      throw new Error(
        `State change inconsistency detected in ${this.beforeState.handler}: ` +
        `Expected ${this.beforeState.key} to change by ${this.expectedDelta}, ` +
        `but changed by ${actualDelta}. ` +
        `This may indicate the handler executed multiple times.`
      )
    }
  }
}

// Framework automatically tracks:
bus.on('TODO_ADD', (payload) => {
  const prev = state.todos.length
  stateTracker.recordPrecondition('TODO_ADD', 'todos.length', prev, 1)

  // ... handler logic

  stateTracker.verifyPostcondition('todos.length', state.todos.length)
})
```

**Pros:**
- Catches the issue at runtime automatically
- Works without developer annotation (framework can inject)

**Cons:**
- Complex to implement generically
- Runtime overhead
- Only works for numeric state changes

## Recommended Implementation Order

1. **Strategy 1: Runtime Handler Execution Tracking** (Immediate - catches issue in development)
2. **Strategy 2: Architectural Fix** (High priority - prevents issue by design)
3. **Strategy 5: Integration Tests** (High priority - prevents regressions)
4. **Strategy 3: Listener Registration Detection** (Medium priority - defense in depth)
5. **Strategy 4: Verification Primitive** (Long term - for formal verification)
6. **Strategy 6: State Invariant Detection** (Long term - advanced feature)

## Additional Systematic Improvements

### Better Error Messages
When postconditions fail, include handler execution context:
```typescript
ensures(state.todos.length === previousCount + 1,
  `Todo count must increase by 1 (was ${previousCount}, now ${state.todos.length}, ` +
  `messageId: ${currentMessageId})`)
```

### Handler Registration Auditing
Log all handler registrations in dev mode:
```typescript
bus.on('TODO_ADD', handler)
// Logs: "Handler 'TODO_ADD' registered (count: 1)"
// If registered again: "WARNING: Handler 'TODO_ADD' registered again (count: 2)"
```

### Framework Self-Verification
The framework itself should verify its own invariants:
- Only one chrome.runtime.onMessage listener per context
- Message IDs are unique
- Handlers registered before messages can be sent
- No duplicate handler registrations (or if allowed, document clearly)
