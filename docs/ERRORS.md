# Error Handling

## Overview

The extension uses a typed error system to provide consistent, informative error handling across all contexts. Errors are first-class types that flow through the message bus with full type safety.

**Key Principles:**
- **Type-Safe Errors** - Custom error classes with metadata
- **Error Codes** - Enum for all error types
- **Consistent Format** - All responses follow `{ success: boolean, error?: string }` pattern
- **Context Preservation** - Errors include source, metadata, and stack traces
- **Graceful Degradation** - Recoverable vs non-recoverable errors

## Error Classes

### Base Error Class

```typescript
// src/shared/types/errors.ts

export class ExtensionError extends Error {
  constructor(
    message: string,
    public code: ErrorCode,
    public metadata?: Record<string, unknown>
  ) {
    super(message)
    this.name = this.constructor.name

    // Maintain proper stack trace
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, this.constructor)
    }
  }

  toJSON() {
    return {
      name: this.name,
      message: this.message,
      code: this.code,
      metadata: this.metadata,
      stack: this.stack,
    }
  }
}
```

### Specific Error Types

```typescript
// Message-related errors
export class MessageTimeoutError extends ExtensionError {
  constructor(messageType: string, timeout: number) {
    super(
      `Message timeout after ${timeout}ms: ${messageType}`,
      ErrorCode.MESSAGE_TIMEOUT,
      { messageType, timeout }
    )
  }
}

export class MessageHandlerError extends ExtensionError {
  constructor(messageType: string, originalError: Error) {
    super(
      `Handler failed for ${messageType}: ${originalError.message}`,
      ErrorCode.HANDLER_ERROR,
      { messageType, originalError: originalError.message }
    )
  }
}

export class HandlerNotFoundError extends ExtensionError {
  constructor(messageType: string) {
    super(
      `No handler registered for message type: ${messageType}`,
      ErrorCode.HANDLER_NOT_FOUND,
      { messageType }
    )
  }
}

// Connection errors
export class PortDisconnectedError extends ExtensionError {
  constructor(portName: string) {
    super(
      `Port disconnected: ${portName}`,
      ErrorCode.PORT_DISCONNECTED,
      { portName }
    )
  }
}

export class PortConnectionError extends ExtensionError {
  constructor(portName: string, reason: string) {
    super(
      `Failed to connect port ${portName}: ${reason}`,
      ErrorCode.PORT_CONNECTION_FAILED,
      { portName, reason }
    )
  }
}

// API errors
export class ApiRequestError extends ExtensionError {
  constructor(endpoint: string, status: number, statusText: string) {
    super(
      `API request failed: ${status} ${statusText}`,
      ErrorCode.API_REQUEST_FAILED,
      { endpoint, status, statusText }
    )
  }
}

export class NetworkError extends ExtensionError {
  constructor(endpoint: string, originalError: Error) {
    super(
      `Network error: ${originalError.message}`,
      ErrorCode.NETWORK_ERROR,
      { endpoint, originalError: originalError.message }
    )
  }
}

// Storage errors
export class StorageError extends ExtensionError {
  constructor(operation: string, originalError: Error) {
    super(
      `Storage ${operation} failed: ${originalError.message}`,
      ErrorCode.STORAGE_ERROR,
      { operation, originalError: originalError.message }
    )
  }
}

// Tab errors
export class TabNotFoundError extends ExtensionError {
  constructor(tabId: number) {
    super(
      `Tab not found: ${tabId}`,
      ErrorCode.TAB_NOT_FOUND,
      { tabId }
    )
  }
}

// Validation errors
export class ValidationError extends ExtensionError {
  constructor(field: string, reason: string) {
    super(
      `Validation failed for ${field}: ${reason}`,
      ErrorCode.VALIDATION_ERROR,
      { field, reason }
    )
  }
}
```

## Error Codes

```typescript
// src/shared/types/errors.ts

export enum ErrorCode {
  // Message errors (1000-1099)
  MESSAGE_TIMEOUT = 1000,
  HANDLER_NOT_FOUND = 1001,
  HANDLER_ERROR = 1002,
  MESSAGE_ROUTING_ERROR = 1003,

  // Connection errors (1100-1199)
  PORT_DISCONNECTED = 1100,
  PORT_CONNECTION_FAILED = 1101,
  PORT_NOT_FOUND = 1102,

  // API errors (1200-1299)
  API_REQUEST_FAILED = 1200,
  NETWORK_ERROR = 1201,
  API_RESPONSE_INVALID = 1202,

  // Storage errors (1300-1399)
  STORAGE_ERROR = 1300,
  STORAGE_QUOTA_EXCEEDED = 1301,

  // Tab errors (1400-1499)
  TAB_NOT_FOUND = 1400,
  TAB_PERMISSION_DENIED = 1401,

  // Validation errors (1500-1599)
  VALIDATION_ERROR = 1500,

  // Unknown/Generic (9999)
  UNKNOWN_ERROR = 9999,
}
```

## Error Propagation

### Through Message Bus

The MessageBus handles errors and transforms them into responses:

```typescript
// src/shared/lib/message-bus.ts

async handleMessage(message: RoutedMessage): Promise<RoutedResponse> {
  const handler = this.handlers.get(message.payload.type)

  if (!handler) {
    this.adapters.logger.warn('No handler registered', {
      type: message.payload.type
    })

    return {
      id: message.id,
      success: false,
      error: 'No handler registered',
      errorCode: ErrorCode.HANDLER_NOT_FOUND,
      timestamp: Date.now(),
    }
  }

  try {
    const data = await handler(message.payload, message)

    return {
      id: message.id,
      success: true,
      data,
      timestamp: Date.now(),
    }
  } catch (error) {
    // Handle ExtensionError with metadata
    if (error instanceof ExtensionError) {
      this.adapters.logger.error(
        'Handler error',
        error,
        {
          messageType: message.payload.type,
          errorCode: error.code,
          ...error.metadata,
        }
      )

      return {
        id: message.id,
        success: false,
        error: error.message,
        errorCode: error.code,
        metadata: error.metadata,
        timestamp: Date.now(),
      }
    }

    // Handle generic errors
    this.adapters.logger.error(
      'Unexpected handler error',
      error instanceof Error ? error : new Error(String(error)),
      { messageType: message.payload.type }
    )

    return {
      id: message.id,
      success: false,
      error: error instanceof Error ? error.message : 'Unknown error',
      errorCode: ErrorCode.UNKNOWN_ERROR,
      timestamp: Date.now(),
    }
  }
}
```

### Response Type

```typescript
// src/shared/types/messages.ts

export type RoutedResponse = {
  id: string
  success: boolean
  timestamp: number
} & (
  | {
      success: true
      data: any
    }
  | {
      success: false
      error: string
      errorCode?: ErrorCode
      metadata?: Record<string, unknown>
    }
)
```

## Error Handling in Handlers

### Basic Try-Catch

```typescript
// src/background/api-client.ts

this.bus.on('API_REQUEST', async (payload) => {
  const { endpoint, method } = payload

  try {
    const response = await this.bus.adapters.fetch.fetch(endpoint, {
      method,
      // ...
    })

    if (!response.ok) {
      throw new ApiRequestError(
        endpoint,
        response.status,
        response.statusText
      )
    }

    return {
      data: await response.json(),
      status: response.status,
    }
  } catch (error) {
    // Network errors
    if (error instanceof TypeError) {
      throw new NetworkError(endpoint, error)
    }

    // Re-throw ExtensionErrors
    if (error instanceof ExtensionError) {
      throw error
    }

    // Wrap unknown errors
    throw new ExtensionError(
      'API request failed',
      ErrorCode.API_REQUEST_FAILED,
      { endpoint, error: String(error) }
    )
  }
})
```

### Validation

```typescript
// src/background/settings-manager.ts

this.bus.on('SETTINGS_UPDATE', async (payload) => {
  const { settings } = payload

  // Validate settings
  if (settings.refreshInterval !== undefined) {
    if (settings.refreshInterval < 1000) {
      throw new ValidationError(
        'refreshInterval',
        'Must be at least 1000ms'
      )
    }
  }

  if (settings.theme !== undefined) {
    if (!['light', 'dark', 'auto'].includes(settings.theme)) {
      throw new ValidationError(
        'theme',
        'Must be light, dark, or auto'
      )
    }
  }

  // Update settings
  await this.updateSettings(settings)

  return { success: true }
})
```

## Error Recovery

### Retry Logic

```typescript
// src/background/api-client.ts

async function fetchWithRetry(
  fetch: FetchAdapter,
  endpoint: string,
  options: RequestInit,
  maxRetries = 3
): Promise<Response> {
  let lastError: Error | null = null

  for (let attempt = 0; attempt < maxRetries; attempt++) {
    try {
      return await fetch.fetch(endpoint, options)
    } catch (error) {
      lastError = error instanceof Error ? error : new Error(String(error))

      if (attempt < maxRetries - 1) {
        // Exponential backoff
        await new Promise(resolve =>
          setTimeout(resolve, Math.pow(2, attempt) * 1000)
        )
      }
    }
  }

  throw new NetworkError(endpoint, lastError!)
}
```

### Fallback Values

```typescript
// src/background/settings-manager.ts

this.bus.on('SETTINGS_GET', async () => {
  try {
    const result = await this.adapters.storage.get('app-settings')
    return { settings: result['app-settings'] || defaultSettings }
  } catch (error) {
    this.adapters.logger.error(
      'Failed to load settings, using defaults',
      error instanceof Error ? error : new Error(String(error))
    )

    // Return defaults on error
    return { settings: defaultSettings }
  }
})
```

### Graceful Degradation

```typescript
// src/background/message-router.ts

private routeMessage(message: RoutedMessage): void {
  try {
    const port = this.getTargetPort(message)

    if (!port) {
      throw new PortNotFoundError(message.target, message.tabId)
    }

    port.postMessage(message)
  } catch (error) {
    if (error instanceof PortNotFoundError) {
      this.adapters.logger.warn('Port not found, queuing message', {
        target: message.target,
        tabId: message.tabId,
      })

      // Queue for later delivery
      this.queueMessage(message)
      return
    }

    // Critical error, can't recover
    this.adapters.logger.error('Failed to route message', error, {
      messageId: message.id,
      target: message.target,
    })

    throw error
  }
}
```

## User-Facing Error Messages

Separate technical errors from user messages:

```typescript
// src/popup/error-display.tsx

function getUserMessage(error: ExtensionError): string {
  switch (error.code) {
    case ErrorCode.NETWORK_ERROR:
      return 'Unable to connect to the server. Please check your internet connection.'

    case ErrorCode.API_REQUEST_FAILED:
      return 'The server returned an error. Please try again later.'

    case ErrorCode.STORAGE_QUOTA_EXCEEDED:
      return 'Storage is full. Please clear some data.'

    case ErrorCode.VALIDATION_ERROR:
      return `Invalid input: ${error.metadata?.reason || 'Please check your input'}`

    case ErrorCode.TAB_NOT_FOUND:
      return 'The requested tab could not be found.'

    default:
      return 'An unexpected error occurred. Please try again.'
  }
}

// Usage in UI
try {
  await sendMessage({ type: 'API_REQUEST', endpoint: '/data', method: 'GET' })
} catch (error) {
  if (error instanceof ExtensionError) {
    showNotification(getUserMessage(error))
  } else {
    showNotification('An unexpected error occurred')
  }
}
```

## Testing Error Scenarios

### Throwing Errors in Tests

```typescript
import { MessageTimeoutError, ErrorCode } from '@/shared/types/errors'

test('MessageBus handles timeout errors', async () => {
  const mockLogger = createMockLogger({ silent: true })
  const adapters = {
    // ... other adapters
    logger: mockLogger,
  }

  const bus = new MessageBus('background', adapters)

  // Don't register a handler - will timeout
  const promise = bus.send(
    { type: 'SETTINGS_GET' },
    { timeout: 100 }
  )

  await expect(promise).rejects.toThrow(MessageTimeoutError)

  // Verify error was logged
  const errorLog = mockLogger._calls.find(call => call.level === 'error')
  expect(errorLog).toBeDefined()
})
```

### Simulating Handler Errors

```typescript
test('MessageBus handles handler errors gracefully', async () => {
  const bus = new MessageBus('background', createMockAdapters())

  // Register handler that throws
  bus.on('SETTINGS_UPDATE', async () => {
    throw new ValidationError('theme', 'Invalid theme value')
  })

  const response = await bus.send({
    type: 'SETTINGS_UPDATE',
    settings: { theme: 'invalid' },
  })

  expect(response).toMatchObject({
    success: false,
    error: expect.stringContaining('Invalid theme value'),
    errorCode: ErrorCode.VALIDATION_ERROR,
  })
})
```

### Testing Error Recovery

```typescript
test('API client retries on failure', async () => {
  const mockFetch = createMockFetch()

  // First two attempts fail
  mockFetch._responses.push({
    ok: false,
    status: 500,
    statusText: 'Server Error',
  })
  mockFetch._responses.push({
    ok: false,
    status: 500,
    statusText: 'Server Error',
  })
  // Third attempt succeeds
  mockFetch._responses.push({
    ok: true,
    status: 200,
    json: async () => ({ data: 'success' }),
  })

  const result = await fetchWithRetry(
    mockFetch,
    'https://api.example.com/data',
    {},
    3
  )

  expect(result.status).toBe(200)
  expect(mockFetch._calls).toHaveLength(3)
})
```

## Best Practices

### 1. Use Specific Error Types

```typescript
// ✅ Good - specific error with metadata
throw new ApiRequestError(endpoint, response.status, response.statusText)

// ❌ Bad - generic error loses context
throw new Error(`API request failed: ${response.status}`)
```

### 2. Include Error Context

```typescript
// ✅ Good - rich metadata
throw new MessageTimeoutError(messageType, timeout)

// ❌ Bad - loses timeout value
throw new Error(`Message timeout: ${messageType}`)
```

### 3. Log Before Throwing

```typescript
// ✅ Good - log for debugging, then throw for handling
this.logger.error('Port disconnected unexpectedly', error, { port: port.name })
throw new PortDisconnectedError(port.name)
```

### 4. Don't Swallow Errors

```typescript
// ❌ Bad - silent failure
try {
  await riskyOperation()
} catch (error) {
  // Nothing - error is lost
}

// ✅ Good - log and handle
try {
  await riskyOperation()
} catch (error) {
  this.logger.error('Operation failed', error)
  throw new ExtensionError('Operation failed', ErrorCode.UNKNOWN_ERROR)
}
```

### 5. Provide Recovery Hints

```typescript
// ✅ Good - error suggests recovery
throw new ValidationError(
  'email',
  'Must be a valid email address (e.g., user@example.com)'
)

// ❌ Bad - no hint how to fix
throw new ValidationError('email', 'Invalid')
```

### 6. Chain Errors

```typescript
// ✅ Good - preserves original error
catch (error) {
  throw new NetworkError(
    endpoint,
    error instanceof Error ? error : new Error(String(error))
  )
}
```

## Common Patterns

### Guard Clauses with Errors

```typescript
function processMessage(message: RoutedMessage) {
  if (!message.payload) {
    throw new ValidationError('payload', 'Payload is required')
  }

  if (!message.target) {
    throw new ValidationError('target', 'Target context is required')
  }

  // Process message...
}
```

### Error Boundaries in UI

```typescript
// src/popup/ErrorBoundary.tsx

class ErrorBoundary extends Component {
  state = { error: null }

  static getDerivedStateFromError(error: Error) {
    return { error }
  }

  componentDidCatch(error: Error, errorInfo: any) {
    if (error instanceof ExtensionError) {
      this.props.logger.error('UI error', error, {
        component: errorInfo.componentStack,
        errorCode: error.code,
      })
    }
  }

  render() {
    if (this.state.error) {
      return <ErrorDisplay error={this.state.error} />
    }

    return this.props.children
  }
}
```

## See Also

- [LOGGING.md](./LOGGING.md) - Logging errors with context
- [MESSAGING.md](./MESSAGING.md) - Error responses in messages
- [TESTING.md](./TESTING.md) - Testing error scenarios
