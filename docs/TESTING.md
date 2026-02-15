# Testing Guide

## Overview

This extension achieves 100% type safety and comprehensive test coverage through:
- **Adapter Pattern**: All external APIs wrapped for testability
- **Dependency Injection**: Services accept optional adapters/bus for testing
- **Mock Directory Structure**: Mirrors production code organization
- **Path Aliases**: Uses `@/` imports for consistency
- **Zero Type Casts**: Proper typed mocks eliminate `as any`

## Table of Contents

1. [Test Architecture](#test-architecture)
2. [Mock Adapters](#mock-adapters)
3. [Unit Testing Patterns](#unit-testing-patterns)
4. [Integration Testing Patterns](#integration-testing-patterns)
5. [Common Patterns](#common-patterns)
6. [Testing Utilities](#testing-utilities)
7. [Best Practices](#best-practices)

---

## Test Architecture

### Directory Structure

```
tests/
├── helpers/
│   ├── adapters/           # Mock implementations mirror src/shared/adapters/
│   │   ├── index.ts        # Main exports with createMockAdapters()
│   │   ├── runtime.mock.ts
│   │   ├── storage.mock.ts
│   │   ├── tabs.mock.ts
│   │   ├── window.mock.ts
│   │   ├── offscreen.mock.ts
│   │   ├── context-menus.mock.ts
│   │   └── fetch.mock.ts
│   └── test-utils.ts       # Shared test utilities
├── unit/
│   ├── *.test.ts           # Unit tests (isolated functionality)
│   └── contexts/
│       └── content.test.ts
└── integration/
    └── cross-context.test.ts  # Integration tests (multiple components)
```

### Import Patterns

**Always use path aliases:**

```typescript
// ✅ Good - path alias
import { MessageBus } from '@/shared/lib/message-bus'
import { createMockAdapters } from '../helpers/adapters'

// ❌ Bad - relative paths
import { MessageBus } from '../../src/shared/lib/message-bus'
```

---

## Mock Adapters

### Overview

Mock adapters extend production adapter interfaces with test-specific internals:

```typescript
export interface MockRuntime extends RuntimeAdapter {
  _connectListeners: Array<(port: PortAdapter) => void>
  _messageListeners: Array<(message: any, sender: any, sendResponse: any) => void>
}
```

### Creating Mocks

**Two approaches:**

#### 1. Use `createMockAdapters()` - Simple Cases

When you don't need access to mock internals:

```typescript
import { createMockAdapters } from '../helpers/adapters'

test('Simple test', async () => {
  const adapters = createMockAdapters()
  const bus = new MessageBus('background', adapters)

  // Use bus normally
})
```

#### 2. Create Mocks Directly - Complex Cases

When you need access to mock internals (e.g., `_connectListeners`):

```typescript
import {
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
  createMockOffscreen,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  type MockRuntime,
} from '../helpers/adapters'
import type { ExtensionAdapters } from '@/shared/adapters'

test('Complex test', () => {
  // Create the mock you need separately
  const mockRuntime = createMockRuntime()

  // Compose full adapter set
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  }

  // Now you can access internals
  mockRuntime._connectListeners.forEach(listener => {
    listener(port)
  })
})
```

### Available Mock Factories

```typescript
// Mock adapters
createMockRuntime(): MockRuntime
createMockStorageArea(): MockStorageArea
createMockTabs(): MockTabs
createMockWindow(): MockWindow
createMockOffscreen(): MockOffscreen
createMockContextMenus(): MockContextMenus
createMockFetch(): MockFetch
createMockLogger(options?: { silent?: boolean }): MockLogger

// Convenience functions
createMockPort(name: string): MockPort
createMockAdapters(): ExtensionAdapters  // All adapters at once
createMockChrome(): MockChrome            // Chrome-like API grouping
```

### Testing with MockLogger

The `MockLogger` adapter is unique in that it captures all log calls for assertions and remains silent by default to avoid test output noise:

```typescript
import { createMockLogger, type MockLogger } from '../helpers/adapters'

test('Verify logging behavior', () => {
  const mockLogger = createMockLogger({ silent: true })

  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: mockLogger,
  }

  const bus = new MessageBus('background', adapters)

  // Code that logs something
  bus.adapters.logger.info('Test message', { foo: 'bar' })

  // Assert log was called
  expect(mockLogger._calls).toHaveLength(1)
  expect(mockLogger._calls[0]).toMatchObject({
    level: 'info',
    message: 'Test message',
    context: { foo: 'bar' }
  })
})
```

**MockLogger Options:**

- `silent: true` (default) - Suppress console output during tests
- `silent: false` - Show logs in console (useful for debugging failing tests)

**MockLogger Internals:**

```typescript
export interface MockLogger extends LoggerAdapter {
  _calls: LogCall[]  // Array of all captured log calls
  _clear(): void     // Clear captured calls (useful in beforeEach/afterEach)
}

export interface LogCall {
  level: LogLevel
  message: string
  context?: Record<string, unknown>
  error?: Error
  timestamp: number
}
```

**Common Patterns:**

```typescript
// Clear logs between tests
let mockLogger: MockLogger

beforeEach(() => {
  mockLogger = createMockLogger({ silent: true })
})

afterEach(() => {
  mockLogger._clear()
})

// Enable logs for debugging
test('Debug failing test', () => {
  const mockLogger = createMockLogger({ silent: false })
  // Logs will appear in console
})

// Assert specific log was called
test('Error logged on failure', () => {
  // ... trigger error ...

  const errorLog = mockLogger._calls.find(call => call.level === 'error')
  expect(errorLog).toBeDefined()
  expect(errorLog?.message).toContain('Failed')
})
```

See [LOGGING.md](./LOGGING.md) for comprehensive logging documentation.

---

## Unit Testing Patterns

### Testing Services with Dependency Injection

All background services accept optional `MessageBus` or adapters:

```typescript
import { ApiClient } from '@/background/api-client'
import { MessageBus } from '@/shared/lib/message-bus'
import { createMockFetch, type MockFetch } from '../helpers/adapters'

let mockFetch: MockFetch
let bus: MessageBus

beforeEach(() => {
  mockFetch = createMockFetch()

  const adapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: mockFetch,  // ✅ No cast needed!
    logger: createMockLogger(),
  }

  bus = new MessageBus('background', adapters)
})

test('ApiClient - handles API_REQUEST', async () => {
  const client = new ApiClient(bus)

  // Queue a mock response
  mockFetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ 'content-type': 'application/json' }),
    statusText: 'OK',
    json: async () => ({ data: 'test' }),
  })

  const response = await bus.send({
    type: 'API_REQUEST',
    endpoint: 'https://api.example.com/test',
    method: 'GET',
  })

  expect(response.status).toBe(200)
  expect(mockFetch._calls).toHaveLength(1)
})
```

### Testing Message Handlers

Use properly typed mock functions:

```typescript
import { mock } from 'bun:test'

test('MessageBus - handler receives correct payload', async () => {
  // ✅ Good - properly typed with both parameters
  const handler = mock(async (payload, _message) => {
    expect(payload.type).toBe('SETTINGS_GET')
    return { settings: {} }
  })

  bus.on('SETTINGS_GET', handler)

  await bus.send({ type: 'SETTINGS_GET' })
  expect(handler).toHaveBeenCalled()
})
```

### Testing with Spies

Type spies explicitly to avoid casts:

```typescript
test('MessageBus - broadcast calls sendMessage', () => {
  // ✅ Good - explicitly typed
  const sendSpy = mock<typeof bus.broadcast>(() => {})
  const originalBroadcast = bus.broadcast
  bus.broadcast = sendSpy

  bus.broadcast({
    type: 'SIGNAL_UPDATE',
    signalId: 'test',
    value: {},
    source: 'background',
  })

  expect(sendSpy).toHaveBeenCalled()

  // Restore
  bus.broadcast = originalBroadcast
})
```

### Testing MessageRouter

Access mock runtime internals to simulate port connections:

```typescript
import { MessageRouter } from '@/background/message-router'
import { createMockRuntime, createMockPort, type MockRuntime } from '../helpers/adapters'

let mockRuntime: MockRuntime
let router: MessageRouter

beforeEach(() => {
  mockRuntime = createMockRuntime()
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  }

  const bus = new MessageBus('background', adapters)
  router = new MessageRouter(bus)
})

test('MessageRouter - registers content script port', () => {
  const port = createMockPort('content-123')

  // Simulate port connection
  mockRuntime._connectListeners.forEach(listener => {
    listener(port)
  })

  expect(router['contentPorts'].has(123)).toBe(true)
})
```

---

## Integration Testing Patterns

### Cross-Context Communication

Integration tests verify multiple components working together:

```typescript
import { MessageBus } from '@/shared/lib/message-bus'
import { MessageRouter } from '@/background/message-router'
import {
  createMockRuntime,
  createMockPort,
  type MockRuntime,
} from '../helpers/adapters'

// Helper function to simulate port connections
function simulatePortConnection(
  mockRuntime: MockRuntime,
  port: ReturnType<typeof createMockPort>
) {
  mockRuntime._connectListeners.forEach(listener => listener(port))
}

test('Integration - Background to Content communication', async () => {
  const mockRuntime = createMockRuntime()
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  }

  const backgroundBus = new MessageBus('background', adapters)
  const router = new MessageRouter(backgroundBus)

  const contentPort = createMockPort('content-123')

  // Spy BEFORE connecting to avoid infinite loops
  const postMessageSpy = mock((msg: any) => {
    // Don't trigger listeners to avoid loop
  })
  contentPort.postMessage = postMessageSpy

  simulatePortConnection(mockRuntime, contentPort)

  router['routeMessage']({
    id: 'test-id',
    source: 'background',
    target: 'content',
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: 'DOM_QUERY', selector: '.test' },
  })

  expect(postMessageSpy).toHaveBeenCalled()
})
```

### Shared Mock Instances

When testing cross-context state (e.g., storage), use the same mock instance:

```typescript
test('Integration - Settings synchronization', async () => {
  const mockStorage = createMockStorageArea()
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: mockStorage,  // ✅ Same instance for all buses
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  }

  await mockStorage.set({
    'app-settings': { debugMode: true, theme: 'dark' },
  })

  const backgroundBus = new MessageBus('background', adapters)
  const popupBus = new MessageBus('popup', adapters)

  // Background handler uses same storage
  backgroundBus.on('SETTINGS_GET', async () => {
    const result = await mockStorage.get('app-settings')
    return { settings: result['app-settings'] }
  })

  // Popup reads from same storage through handler
  const response = await popupBus.send({ type: 'SETTINGS_GET' })
  expect(response.settings).toEqual({ debugMode: true, theme: 'dark' })
})
```

---

## Common Patterns

### Lazy Initialization in Production

The `syncedSignal` pattern uses lazy initialization to avoid `chrome is not defined` errors:

```typescript
// src/shared/lib/signal-sync.ts

export function syncedSignal<T>(initialValue: T, options: SyncedSignalOptions) {
  const signal = _signal<T>(initialValue)

  // Lazy bus initialization - don't create until chrome is available
  let bus: MessageBus | null = null
  const getBus = () => {
    if (!bus) {
      bus = options.bus || (
        typeof chrome !== 'undefined'
          ? getMessageBus(currentContext)
          : null
      )
    }
    return bus
  }

  // Use getBus() instead of creating bus at module level
  signal.subscribe((value) => {
    const messageBus = getBus()
    if (messageBus) {
      messageBus.broadcast(/* ... */)
    }
  })

  return signal
}
```

### Dependency Injection in Services

All services accept optional dependencies for testing:

```typescript
// src/background/api-client.ts

export class ApiClient {
  private bus: MessageBus

  constructor(bus?: MessageBus) {
    // Use injected bus or get global instance
    this.bus = bus || getMessageBus('background')
    this.setupHandlers()
  }
}

// Usage in tests
test('ApiClient test', () => {
  const mockBus = new MessageBus('background', mockAdapters)
  const client = new ApiClient(mockBus)  // Inject test bus
})

// Usage in production
const client = new ApiClient()  // Uses global bus
```

### Avoiding Infinite Loops in Tests

When testing message routing, spy on `postMessage` BEFORE connecting the port:

```typescript
test('Router sends message to port', () => {
  const port = createMockPort('content-123')

  // ✅ Spy BEFORE connecting
  const spy = mock((msg: any) => {
    // Don't trigger listeners to avoid loop
  })
  port.postMessage = spy

  // Now connect (router will add its own listener)
  simulatePortConnection(mockRuntime, port)

  router['routeMessage'](message)
  expect(spy).toHaveBeenCalled()
})
```

---

## Testing Utilities

### Available Utilities

```typescript
// tests/helpers/test-utils.ts

// Create routed message fixtures
createMockRoutedMessage<T extends ExtensionMessage>(
  payload: T,
  overrides?: Partial<Omit<RoutedMessage<T>, 'payload'>>
): RoutedMessage<T>

// Async delays
waitFor(ms: number): Promise<void>

// Polling assertions
waitForCondition(
  condition: () => boolean,
  timeout?: number,
  interval?: number
): Promise<void>

// Compile-time type checking
expectType<T>(value: T): void
```

### Usage Examples

```typescript
import { createMockRoutedMessage, waitFor, waitForCondition } from '../helpers/test-utils'

test('Using test utilities', async () => {
  // Create fixture
  const message = createMockRoutedMessage(
    { type: 'SETTINGS_GET' },
    { source: 'popup', target: 'background' }
  )

  // Wait for async operations
  await waitFor(10)

  // Poll for condition
  await waitForCondition(
    () => handler.mock.calls.length > 0,
    1000  // timeout
  )
})
```

---

## Best Practices

### ✅ Do

1. **Use path aliases for all imports**
   ```typescript
   import { MessageBus } from '@/shared/lib/message-bus'
   ```

2. **Create mocks directly when you need internals**
   ```typescript
   const mockRuntime = createMockRuntime()
   mockRuntime._connectListeners.forEach(/* ... */)
   ```

3. **Use properly typed mock functions**
   ```typescript
   const handler = mock(async (payload, _message) => {
     return { settings: {} }
   })
   ```

4. **Share mock instances for integration tests**
   ```typescript
   const mockStorage = createMockStorageArea()
   // Use same mockStorage in all buses
   ```

5. **Inject dependencies in tests**
   ```typescript
   const client = new ApiClient(mockBus)
   ```

### ❌ Don't

1. **Don't use type casts**
   ```typescript
   // ❌ Bad
   const handler = mock(async (payload: any) => {}) as any

   // ✅ Good
   const handler = mock(async (payload, _message) => {})
   ```

2. **Don't use relative paths for src imports**
   ```typescript
   // ❌ Bad
   import { MessageBus } from '../../src/shared/lib/message-bus'

   // ✅ Good
   import { MessageBus } from '@/shared/lib/message-bus'
   ```

3. **Don't create separate mock instances unintentionally**
   ```typescript
   // ❌ Bad - different storage instances
   const mockChrome = createMockChrome()
   const adapters = createMockAdapters()
   // These have different storage!

   // ✅ Good - shared storage
   const mockStorage = createMockStorageArea()
   const adapters = { storage: mockStorage, /* ... */ }
   ```

4. **Don't spy after connecting ports**
   ```typescript
   // ❌ Bad - can cause infinite loops
   simulatePortConnection(mockRuntime, port)
   port.postMessage = spy

   // ✅ Good
   port.postMessage = spy
   simulatePortConnection(mockRuntime, port)
   ```

5. **Don't call chrome APIs at module level**
   ```typescript
   // ❌ Bad - runs before chrome is available
   const bus = getMessageBus('background')
   const signal = syncedSignal(0, { key: 'count' })

   // ✅ Good - lazy initialization
   let bus: MessageBus | null = null
   const getBus = () => {
     if (!bus) bus = getMessageBus('background')
     return bus
   }
   ```

---

## Running Tests

```bash
# Run all tests
bun test

# Run specific test file
bun test tests/unit/message-bus.test.ts

# Run tests matching pattern
bun test -t "MessageBus"

# Watch mode
bun test --watch
```

### Test Configuration

Tests are configured in `bunfig.toml`:

```toml
[test]
exclude = [
  "tests/e2e/**/*.spec.ts"  # E2E tests run separately with Playwright
]
```

---

## Coverage

Current test coverage: **126 tests, 100% passing**

- ✅ Unit tests for all adapters
- ✅ Unit tests for message bus
- ✅ Unit tests for message router
- ✅ Unit tests for background handlers
- ✅ Unit tests for signal synchronization
- ✅ Integration tests for cross-context communication
- ✅ Zero type casts (`as any`) in test code
- ✅ Full type safety with TypeScript strict mode

E2E tests with Playwright are run separately for browser-based scenarios.
