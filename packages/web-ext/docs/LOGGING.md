# Logging

## Overview

Logging in the extension uses a **message-based centralized architecture** where all contexts send LOG messages to a LogStore service running in the background. This provides unified log management, cross-context visibility, and powerful querying capabilities.

**Key Principles:**
- **Centralized** - All logs stored in background LogStore
- **Message-Based** - Uses MessageBus to send LOG messages
- **No Environment Detection** - Just inject different adapters (MockLogger for tests, MessageLoggerAdapter for production)
- **Consistent Interface** - Same logging API everywhere
- **Testable** - Mock logger captures calls locally without sending messages
- **Structured Context** - Pass metadata objects for rich logging

## Architecture

```
┌─────────────┐        LOG message        ┌────────────────┐
│   Content   │───────────────────────────>│                │
│   Script    │                            │   Background   │
└─────────────┘                            │   LogStore     │
                                           │                │
┌─────────────┐        LOG message        │  • Circular    │
│    Popup    │───────────────────────────>│    Buffer      │
└─────────────┘                            │  • Filtering   │
                                           │  • Export      │
┌─────────────┐        LOG message        │                │
│   DevTools  │───────────────────────────>│                │
└─────────────┘                            └────────────────┘
                                                    │
                                                    v
                                           ┌────────────────┐
                                           │  LOGS_GET      │
                                           │  LOGS_CLEAR    │
                                           │  LOGS_EXPORT   │
                                           └────────────────┘
```

## Logger Adapter Interface

```typescript
// src/shared/adapters/logger.adapter.ts

export interface LoggerAdapter {
  /**
   * Debug-level logging (verbose, development info)
   */
  debug(message: string, context?: Record<string, unknown>): void

  /**
   * Info-level logging (general information)
   */
  info(message: string, context?: Record<string, unknown>): void

  /**
   * Warning-level logging (non-critical issues)
   */
  warn(message: string, context?: Record<string, unknown>): void

  /**
   * Error-level logging (errors and exceptions)
   */
  error(message: string, error?: Error, context?: Record<string, unknown>): void

  /**
   * Log with explicit level
   */
  log(level: LogLevel, message: string, context?: Record<string, unknown>): void
}

export type LogLevel = 'debug' | 'info' | 'warn' | 'error'
```

## Message Types

```typescript
// src/shared/types/messages.ts

export type LogLevel = 'debug' | 'info' | 'warn' | 'error'

export type LogEntry = {
  id: string
  level: LogLevel
  message: string
  context?: Record<string, unknown>
  error?: string
  stack?: string
  source: Context
  timestamp: number
}

// In ExtensionMessage union:
| { type: 'LOG'; level: LogLevel; message: string; context?: Record<string, unknown>; error?: string; stack?: string; source: Context; timestamp: number }
| { type: 'LOGS_GET'; filters?: { level?: LogLevel; source?: Context; since?: number; limit?: number } }
| { type: 'LOGS_CLEAR' }
| { type: 'LOGS_EXPORT' }
```

## Production Implementation

### MessageLoggerAdapter

The production logger sends LOG messages via the MessageBus:

```typescript
// src/shared/adapters/logger.adapter.ts

export class MessageLoggerAdapter implements LoggerAdapter {
  constructor(
    private runtime: RuntimeAdapter,
    private sourceContext: Context,
    private options?: MessageLoggerOptions
  ) {}

  info(message: string, context?: Record<string, unknown>): void {
    this.sendLog('info', message, context)
  }

  error(message: string, error?: Error, context?: Record<string, unknown>): void {
    this.sendLog('error', message, context, error)
  }

  // ... similar for debug, warn, log

  private sendLog(
    level: LogLevel,
    message: string,
    context?: Record<string, unknown>,
    error?: Error
  ): void {
    // Send LOG message via runtime (fire-and-forget)
    this.runtime
      .sendMessage({
        type: 'LOG',
        level,
        message,
        context,
        error: error?.message,
        stack: error?.stack,
        source: this.sourceContext,
        timestamp: Date.now(),
      })
      .catch(() => {
        // Fallback to console if messaging fails
        if (this.options?.fallbackToConsole !== false) {
          console[level](message, context, error)
        }
      })
  }
}
```

**Key Design Decisions:**
- Uses `RuntimeAdapter` directly (not MessageBus) to avoid circular dependency
- Fire-and-forget: doesn't wait for response
- Fallback to console if message sending fails
- Includes source context automatically

### LogStore Service

The background LogStore collects and manages logs from all contexts:

```typescript
// src/background/log-store.ts

export class LogStore {
  private bus: MessageBus
  private logs: LogEntry[] = []
  private maxLogs: number

  constructor(bus?: MessageBus, options?: LogStoreOptions) {
    this.bus = bus || getMessageBus('background')
    this.maxLogs = options?.maxLogs || 1000
    this.setupHandlers()
  }

  private setupHandlers(): void {
    // Handle LOG messages from all contexts
    this.bus.on('LOG', async (payload) => {
      const entry: LogEntry = {
        id: crypto.randomUUID(),
        level: payload.level,
        message: payload.message,
        context: payload.context,
        error: payload.error,
        stack: payload.stack,
        source: payload.source,
        timestamp: payload.timestamp,
      }

      // Add to circular buffer
      this.logs.push(entry)
      if (this.logs.length > this.maxLogs) {
        this.logs.shift()  // Remove oldest
      }

      return { success: true }
    })

    // Handle LOGS_GET with filtering
    this.bus.on('LOGS_GET', async (payload) => {
      let filtered = this.logs

      if (payload.filters?.level) {
        filtered = filtered.filter(log => log.level === payload.filters!.level)
      }

      if (payload.filters?.source) {
        filtered = filtered.filter(log => log.source === payload.filters!.source)
      }

      if (payload.filters?.since) {
        filtered = filtered.filter(log => log.timestamp >= payload.filters!.since!)
      }

      if (payload.filters?.limit) {
        filtered = filtered.slice(-payload.filters.limit)
      }

      return { logs: filtered }
    })

    // Handle LOGS_CLEAR
    this.bus.on('LOGS_CLEAR', async () => {
      const count = this.logs.length
      this.logs = []
      return { success: true, count }
    })

    // Handle LOGS_EXPORT
    this.bus.on('LOGS_EXPORT', async () => {
      const json = JSON.stringify(this.logs, null, 2)
      return { json, count: this.logs.length }
    })
  }
}
```

**Features:**
- **Circular Buffer**: Keeps last N logs (default 1000)
- **Filtering**: By level, source, timestamp, limit
- **Export**: JSON export of all logs
- **Clear**: Remove all logs

### Initialization

Initialize LogStore early in background script:

```typescript
// src/background/index.ts

// Bootstrap logging (before LogStore exists)
console.log('[Background] Service worker starting...')

// Initialize LogStore FIRST
const logStore = new LogStore()

// Get message bus (now logger is available)
const bus = getMessageBus('background')

// Rest of initialization
bus.adapters.logger.info('Service worker ready')
```

## Test Implementation

The test logger captures calls locally without sending messages:

```typescript
// tests/helpers/adapters/logger.mock.ts

export interface LogCall {
  level: LogLevel
  message: string
  context?: Record<string, unknown>
  error?: Error
  timestamp: number
}

export interface MockLogger extends LoggerAdapter {
  _calls: LogCall[]
  _clear(): void
}

export function createMockLogger(options?: { silent?: boolean }): MockLogger {
  const calls: LogCall[] = []
  const silent = options?.silent ?? true

  return {
    debug(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'debug', message, context, timestamp: Date.now() })
      if (!silent) console.debug(message, context)
    },

    info(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'info', message, context, timestamp: Date.now() })
      if (!silent) console.info(message, context)
    },

    warn(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'warn', message, context, timestamp: Date.now() })
      if (!silent) console.warn(message, context)
    },

    error(message: string, error?: Error, context?: Record<string, unknown>): void {
      calls.push({ level: 'error', message, error, context, timestamp: Date.now() })
      if (!silent) console.error(message, context, error)
    },

    log(level: LogLevel, message: string, context?: Record<string, unknown>): void {
      calls.push({ level, message, context, timestamp: Date.now() })
      if (!silent) console[level](message, context)
    },

    // Test-only internals
    _calls: calls,
    _clear() {
      calls.length = 0
    },
  }
}
```

## Integration with Adapters

Add the logger to the adapter interface:

```typescript
// src/shared/adapters/index.ts

export interface ExtensionAdapters {
  runtime: RuntimeAdapter
  storage: StorageAdapter
  tabs: TabsAdapter
  window: WindowAdapter
  offscreen: OffscreenAdapter
  contextMenus: ContextMenusAdapter
  fetch: FetchAdapter
  logger: LoggerAdapter  // ← 8th adapter
}

export function createChromeAdapters(
  context: Context,
  options?: CreateChromeAdaptersOptions
): ExtensionAdapters {
  const runtime = new ChromeRuntimeAdapter()
  return {
    runtime,
    storage: new ChromeStorageAdapter(),
    tabs: new ChromeTabsAdapter(),
    window: new ChromeWindowAdapter(),
    offscreen: new ChromeOffscreenAdapter(),
    contextMenus: new ChromeContextMenusAdapter(),
    fetch: new BrowserFetchAdapter(),
    logger: new MessageLoggerAdapter(runtime, context, {
      consoleMirror: options?.consoleMirror,
      fallbackToConsole: true,
    }),
  }
}
```

## Usage in Services

Access the logger through the MessageBus adapters:

```typescript
// src/background/message-router.ts

export class MessageRouter {
  private bus: MessageBus

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus('background')
    this.setupPortConnections()
  }

  private setupPortConnections(): void {
    this.bus.adapters.runtime.onConnect((port) => {
      // ✅ Use logger adapter
      this.bus.adapters.logger.debug('Port connected', { port: port.name })

      const [context, tabIdStr] = port.name.split('-')

      switch (context) {
        case 'content': {
          const tabId = parseInt(tabIdStr)
          this.contentPorts.set(tabId, port)

          port.onDisconnect(() => {
            this.bus.adapters.logger.info('Content port disconnected', { tabId })
            this.contentPorts.delete(tabId)
          })
          break
        }
        // ... other cases
      }
    })
  }

  private routeMessage(message: RoutedMessage): void {
    this.bus.adapters.logger.debug('Routing message', {
      type: message.payload.type,
      source: message.source,
      target: message.target,
      messageId: message.id,
    })

    const port = this.getTargetPort(message)

    if (!port) {
      this.bus.adapters.logger.warn('No port found for target', {
        target: message.target,
        tabId: message.tabId,
      })
      return
    }

    port.postMessage(message)
  }
}
```

## Querying Logs

### Get All Logs

```typescript
const response = await bus.send({ type: 'LOGS_GET' })
console.log(response.logs)  // LogEntry[]
```

### Filter by Level

```typescript
const response = await bus.send({
  type: 'LOGS_GET',
  filters: { level: 'error' }
})
// Returns only error logs
```

### Filter by Source Context

```typescript
const response = await bus.send({
  type: 'LOGS_GET',
  filters: { source: 'content' }
})
// Returns only logs from content scripts
```

### Filter by Timestamp

```typescript
const fiveMinutesAgo = Date.now() - 5 * 60 * 1000

const response = await bus.send({
  type: 'LOGS_GET',
  filters: { since: fiveMinutesAgo }
})
// Returns logs from last 5 minutes
```

### Limit Results

```typescript
const response = await bus.send({
  type: 'LOGS_GET',
  filters: { limit: 50 }
})
// Returns last 50 logs
```

### Combined Filters

```typescript
const response = await bus.send({
  type: 'LOGS_GET',
  filters: {
    level: 'error',
    source: 'background',
    since: Date.now() - 60000,  // Last minute
    limit: 10
  }
})
// Returns last 10 background error logs from the last minute
```

## Exporting Logs

```typescript
const response = await bus.send({ type: 'LOGS_EXPORT' })

// Save to file
const blob = new Blob([response.json], { type: 'application/json' })
const url = URL.createObjectURL(blob)
const a = document.createElement('a')
a.href = url
a.download = `logs-${Date.now()}.json`
a.click()
```

## Clearing Logs

```typescript
const response = await bus.send({ type: 'LOGS_CLEAR' })
console.log(`Cleared ${response.count} logs`)
```

## Testing with Logger

### Type-Safe Mock Adapters

Use `MockExtensionAdapters` type for full type safety without type assertions:

```typescript
import { createMockAdapters, type MockExtensionAdapters } from '../helpers/adapters'

let adapters: MockExtensionAdapters

beforeEach(() => {
  adapters = createMockAdapters()
})

test('Test with logger', () => {
  // Access logger with full type information
  adapters.logger.info('Test message')

  // Access mock-specific methods
  expect(adapters.logger._calls).toHaveLength(1)
  adapters.logger._clear()
})
```

### Silent Logger (Default)

Most tests should use silent logger to avoid noise:

```typescript
import { createMockAdapters } from '../helpers/adapters'

test('MessageRouter handles port connection', () => {
  const adapters = createMockAdapters()  // Includes silent MockLogger
  const bus = new MessageBus('background', adapters)
  const router = new MessageRouter(bus)

  // Test logic... no console output
})
```

### Asserting Log Calls

You can assert that specific logs were created:

```typescript
test('MessageRouter logs port connections', () => {
  const adapters = createMockAdapters()
  const bus = new MessageBus('background', adapters)
  const router = new MessageRouter(bus)

  const port = createMockPort('content-123')
  adapters.runtime._connectListeners.forEach(listener => listener(port))

  // Assert log was called
  expect(adapters.logger._calls).toHaveLength(1)
  expect(adapters.logger._calls[0]).toMatchObject({
    level: 'debug',
    message: 'Port connected',
    context: { port: 'content-123' },
  })
})
```

### Capturing Logs for Debugging

During test development, enable console output:

```typescript
test('Debug failing test', () => {
  const mockLogger = createMockLogger({ silent: false })  // Show logs

  const adapters = {
    ...createMockAdapters(),
    logger: mockLogger,
  }

  // ... test that's failing, logs will show in console
})
```

### Clearing Logs Between Tests

```typescript
import type { MockExtensionAdapters } from '../helpers/adapters'

let adapters: MockExtensionAdapters

beforeEach(() => {
  adapters = createMockAdapters()
})

afterEach(() => {
  adapters.logger._clear()  // Clear captured calls
})
```

## Best Practices

### 1. Log Levels

**Debug** - Verbose information for development:
```typescript
logger.debug('Port message received', {
  messageId: message.id,
  type: message.payload.type
})
```

**Info** - General informational events:
```typescript
logger.info('Settings updated', {
  changedKeys: Object.keys(updates)
})
```

**Warn** - Recoverable issues that might need attention:
```typescript
logger.warn('No handler registered', {
  messageType: message.payload.type
})
```

**Error** - Errors and exceptions:
```typescript
logger.error('Message timeout', error, {
  messageType: message.payload.type,
  timeout: 5000
})
```

### 2. Structured Context

Always pass context objects for rich logging:

```typescript
// ✅ Good - structured context
logger.info('Tab updated', {
  tabId: tab.id,
  url: tab.url,
  status: changeInfo.status,
})

// ❌ Bad - string interpolation loses structure
logger.info(`Tab ${tab.id} updated to ${tab.url} with status ${changeInfo.status}`)
```

### 3. Don't Log Sensitive Data

```typescript
// ✅ Good
logger.info('User authenticated', { userId: user.id })

// ❌ Bad - logs password
logger.debug('Login attempt', { username, password })
```

### 4. Log at Decision Points

```typescript
if (!handler) {
  logger.warn('No handler for message', { type: message.payload.type })
  return { success: false, error: 'No handler' }
}

logger.debug('Handler found, executing', { type: message.payload.type })
const result = await handler(message.payload, message)
```

### 5. Include Error Objects

```typescript
// ✅ Good - includes error object with stack trace
logger.error('Failed to fetch data', error, { endpoint })

// ❌ Bad - loses stack trace
logger.error('Failed to fetch data: ' + error.message, undefined, { endpoint })
```

## Migration Guide

Replace existing console calls with logger:

### Before
```typescript
console.log(`[${this.context}] Port connected: ${port.name}`)
console.warn(`[${this.context}] No handler for: ${type}`)
console.error('[Background] Port disconnected')
```

### After
```typescript
this.bus.adapters.logger.debug('Port connected', { port: port.name })
this.bus.adapters.logger.warn('No handler registered', { type })
this.bus.adapters.logger.info('Port disconnected')
```

### Search and Replace Patterns

1. Find all `console.log` calls
2. Replace with appropriate logger level (debug/info)
3. Extract context from string interpolation to object
4. Find all `console.error` with error objects
5. Pass error as second parameter to logger.error()

## Performance Considerations

### Circular Buffer

The LogStore uses a circular buffer (default 1000 logs) to prevent unlimited memory growth. Adjust if needed:

```typescript
const logStore = new LogStore(bus, { maxLogs: 5000 })
```

### Message Overhead

Logging sends messages which have overhead. For high-frequency operations, consider:

```typescript
// ✅ Good - log summary
logger.debug('Processed batch', {
  count: items.length,
  duration: endTime - startTime
})

// ❌ Bad - logs every item
items.forEach(item => {
  logger.debug('Processing item', { item })
})
```

### Large Objects

Avoid logging huge objects:

```typescript
// ❌ Bad - logs entire object
logger.debug('Received data', { data: hugeDataObject })

// ✅ Good - log summary
logger.debug('Received data', {
  dataSize: hugeDataObject.length,
  firstItem: hugeDataObject[0]
})
```

## See Also

- [ADAPTERS.md](./ADAPTERS.md) - Adapter pattern overview
- [ERRORS.md](./ERRORS.md) - Error handling with logging
- [TESTING.md](./TESTING.md) - Testing with mock logger
- [MESSAGING.md](./MESSAGING.md) - Message-based architecture
