# Type-Safe Messaging System

## Overview

The messaging system provides 100% type-safe, bidirectional communication between all extension contexts with automatic response type inference.

## When to Use Messaging vs State

**Use State Primitives** ([STATE.md](./STATE.md)) **for:**
- ✅ Shared data (settings, user info, preferences)
- ✅ Reactive data that needs UI updates
- ✅ Data that should persist across reloads
- ✅ Data synced across multiple contexts

**Use Messaging for:**
- ✅ Commands and actions (DOM manipulation, API calls)
- ✅ One-off queries that don't need reactivity
- ✅ Operations with side effects
- ✅ Cross-boundary operations (content → page, background → API)
- ✅ Page script operations (page scripts can't use state primitives)

### Examples

```typescript
// ❌ DON'T: Use messages for settings
const response = await $send('SETTINGS_GET', {})
const settings = response.settings

// ✅ DO: Use state for settings
import { settings } from '@/shared/state/app-state'
settings.value.theme // Automatically synced and persisted

// ✅ DO: Use messages for actions
await $send('DOM_QUERY', { selector: '.item' })
await $send('API_REQUEST', { endpoint: '/users', method: 'POST' })
```

## Core Concepts

### 1. Discriminated Union Messages

All messages are typed as a discriminated union:

```typescript
// src/shared/types/messages.ts

export type ExtensionMessage =
  // DOM Operations (handled by Content Script)
  | { type: 'DOM_QUERY'; selector: string }
  | { type: 'DOM_UPDATE'; selector: string; content: string }
  | { type: 'DOM_INSERT'; position: 'beforebegin' | 'afterbegin' | 'beforeend' | 'afterend'; html: string }
  | { type: 'DOM_REMOVE'; selector: string }

  // Page Script Operations (handled by Page Script)
  | { type: 'PAGE_EVAL'; code: string }
  | { type: 'PAGE_GET_VAR'; varName: string }
  | { type: 'PAGE_CALL_FN'; fnName: string; args: unknown[] }
  | { type: 'PAGE_SET_VAR'; varName: string; value: unknown }

  // API Operations (handled by Background)
  | { type: 'API_REQUEST'; endpoint: string; method: 'GET' | 'POST' | 'PUT' | 'DELETE'; body?: unknown; headers?: Record<string, string> }
  | { type: 'API_BATCH'; requests: Array<{ endpoint: string; method: string; body?: unknown }> }

  // Clipboard Operations (handled by Offscreen)
  | { type: 'CLIPBOARD_WRITE'; text: string }
  | { type: 'CLIPBOARD_WRITE_HTML'; html: string }
  | { type: 'CLIPBOARD_WRITE_RICH'; data: { text: string; html: string } }
  | { type: 'CLIPBOARD_READ' }

  // Context Menu (handled by Background)
  | { type: 'CONTEXT_MENU_CLICKED'; menuId: string; info: chrome.contextMenus.OnClickData; tabId: number }
  | { type: 'CONTEXT_MENU_CREATE'; id: string; title: string; contexts: chrome.contextMenus.ContextType[] }
  | { type: 'CONTEXT_MENU_REMOVE'; id: string }

  // State Sync (internal - handled by state primitives)
  | { type: 'STATE_SYNC'; key: string; value: unknown; clock: number }

  // Tab Operations (handled by Background)
  | { type: 'TAB_QUERY'; queryInfo: chrome.tabs.QueryInfo }
  | { type: 'TAB_GET_CURRENT' }
  | { type: 'TAB_RELOAD'; tabId: number }

  // DevTools Operations
  | { type: 'DEVTOOLS_INSPECT_ELEMENT'; selector: string }
  | { type: 'DEVTOOLS_LOG'; level: 'log' | 'warn' | 'error'; message: string; data?: unknown }

  // Logging Operations
  | { type: 'LOG'; level: LogLevel; message: string; context?: Record<string, unknown>; source: Context; timestamp: number }
  | { type: 'LOGS_GET'; filters?: { level?: LogLevel; source?: Context; since?: number; limit?: number } }
  | { type: 'LOGS_CLEAR' }
  | { type: 'LOGS_EXPORT' }
```

### 2. Response Type Mapping

Each message type has a corresponding response type:

```typescript
export type MessageResponse<T extends ExtensionMessage> =
  // DOM Operations
  T extends { type: 'DOM_QUERY' } ? {
    elements: Array<{
      tag: string
      text: string
      html: string
      attrs: Record<string, string>
      rect?: DOMRect
    }>
  } :
  T extends { type: 'DOM_UPDATE' } ? { success: boolean } :
  T extends { type: 'DOM_INSERT' } ? { success: boolean } :
  T extends { type: 'DOM_REMOVE' } ? { success: boolean; count: number } :

  // Page Script Operations
  T extends { type: 'PAGE_EVAL' } ? { result: unknown; error?: string } :
  T extends { type: 'PAGE_GET_VAR' } ? { value: unknown; exists: boolean } :
  T extends { type: 'PAGE_CALL_FN' } ? { result: unknown; error?: string } :
  T extends { type: 'PAGE_SET_VAR' } ? { success: boolean } :

  // API Operations
  T extends { type: 'API_REQUEST' } ? {
    data: unknown
    status: number
    statusText: string
    headers: Record<string, string>
    error?: string
  } :
  T extends { type: 'API_BATCH' } ? {
    results: Array<{ data: unknown; status: number; error?: string }>
  } :

  // Clipboard Operations
  T extends { type: 'CLIPBOARD_WRITE' } ? { success: boolean } :
  T extends { type: 'CLIPBOARD_WRITE_HTML' } ? { success: boolean } :
  T extends { type: 'CLIPBOARD_WRITE_RICH' } ? { success: boolean } :
  T extends { type: 'CLIPBOARD_READ' } ? { text: string } :

  // Context Menu
  T extends { type: 'CONTEXT_MENU_CLICKED' } ? void :
  T extends { type: 'CONTEXT_MENU_CREATE' } ? { success: boolean } :
  T extends { type: 'CONTEXT_MENU_REMOVE' } ? { success: boolean } :

  // State Sync (internal)
  T extends { type: 'STATE_SYNC' } ? undefined :

  // Tab Operations
  T extends { type: 'TAB_QUERY' } ? { tabs: chrome.tabs.Tab[] } :
  T extends { type: 'TAB_GET_CURRENT' } ? { tab: chrome.tabs.Tab } :
  T extends { type: 'TAB_RELOAD' } ? { success: boolean } :

  // DevTools Operations
  T extends { type: 'DEVTOOLS_INSPECT_ELEMENT' } ? { success: boolean } :
  T extends { type: 'DEVTOOLS_LOG' } ? undefined :

  // Logging Operations
  T extends { type: 'LOG' } ? { success: boolean } :
  T extends { type: 'LOGS_GET' } ? { logs: LogEntry[] } :
  T extends { type: 'LOGS_CLEAR' } ? { success: boolean; count: number } :
  T extends { type: 'LOGS_EXPORT' } ? { json: string; count: number } :

  undefined
```

### 3. Message Handler Mapping

Defines which context handles which message type:

```typescript
export type MessageHandler = {
  'DOM_QUERY': 'content'
  'DOM_UPDATE': 'content'
  'DOM_INSERT': 'content'
  'DOM_REMOVE': 'content'

  'PAGE_EVAL': 'page'
  'PAGE_GET_VAR': 'page'
  'PAGE_CALL_FN': 'page'
  'PAGE_SET_VAR': 'page'

  'API_REQUEST': 'background'
  'API_BATCH': 'background'

  'CLIPBOARD_WRITE': 'offscreen'
  'CLIPBOARD_WRITE_HTML': 'offscreen'
  'CLIPBOARD_WRITE_RICH': 'offscreen'
  'CLIPBOARD_READ': 'offscreen'

  'CONTEXT_MENU_CLICKED': 'background'
  'CONTEXT_MENU_CREATE': 'background'
  'CONTEXT_MENU_REMOVE': 'background'

  'STATE_SYNC': 'broadcast'

  'TAB_QUERY': 'background'
  'TAB_GET_CURRENT': 'background'
  'TAB_RELOAD': 'background'

  'DEVTOOLS_INSPECT_ELEMENT': 'content'
  'DEVTOOLS_LOG': 'background'

  'LOG': 'background'
  'LOGS_GET': 'background'
  'LOGS_CLEAR': 'background'
  'LOGS_EXPORT': 'background'
}

export type Context = 'background' | 'content' | 'page' | 'devtools' | 'popup' | 'options' | 'offscreen'
```

### 4. Routed Message Envelope

Every message is wrapped in a routing envelope:

```typescript
export type RoutedMessage<T extends ExtensionMessage = ExtensionMessage> = {
  id: string                    // Unique correlation ID (UUID)
  source: Context               // Which context sent it
  target: Context | 'broadcast' // Where it should go
  tabId?: number               // Required for per-tab contexts (content, page, devtools)
  timestamp: number            // When it was sent
  payload: T                   // The actual message
}

export type RoutedResponse<T extends ExtensionMessage = ExtensionMessage> = {
  id: string                    // Matches request ID
  success: boolean             // Whether operation succeeded
  data?: MessageResponse<T>    // Response data (typed based on request)
  error?: string               // Error message if failed
  timestamp: number            // When response was sent
}
```

### 5. Settings Schema

```typescript
export type Settings = {
  theme: 'light' | 'dark' | 'auto'
  autoSync: boolean
  debugMode: boolean
  notifications: boolean
  apiEndpoint: string
  refreshInterval: number
}

export const defaultSettings: Settings = {
  theme: 'auto',
  autoSync: true,
  debugMode: false,
  notifications: true,
  apiEndpoint: 'https://api.example.com',
  refreshInterval: 60000
}
```

## MessageBus Implementation

```typescript
// src/shared/lib/message-bus.ts

import type {
  ExtensionMessage,
  MessageResponse,
  RoutedMessage,
  RoutedResponse,
  Context,
  MessageHandler
} from '../types/messages'
import type { ExtensionAdapters } from '../adapters'
import { adapters as defaultAdapters } from '../adapters'

type PendingRequest = {
  resolve: (value: any) => void
  reject: (error: Error) => void
  timestamp: number
  timeout: NodeJS.Timeout
}

type Handler = (payload: any, message: RoutedMessage) => Promise<any>

export class MessageBus {
  private context: Context
  private adapters: ExtensionAdapters
  private pendingRequests = new Map<string, PendingRequest>()
  private handlers = new Map<string, Handler>()
  private port: ReturnType<ExtensionAdapters['runtime']['connect']> | null = null
  private messageListener: ((message: any, sender: any, sendResponse: any) => void) | null = null

  constructor(context: Context, adapters: ExtensionAdapters = defaultAdapters) {
    this.context = context
    this.adapters = adapters
    this.setupListeners()
  }

  /**
   * Send a message with full type safety.
   * Response type is automatically inferred from message type.
   */
  async send<T extends ExtensionMessage>(
    payload: T,
    options?: {
      target?: Context
      tabId?: number
      timeout?: number
    }
  ): Promise<MessageResponse<T>> {
    const id = crypto.randomUUID()
    const target = options?.target || this.inferTarget(payload.type)

    const message: RoutedMessage<T> = {
      id,
      source: this.context,
      target,
      tabId: options?.tabId,
      timestamp: Date.now(),
      payload
    }

    return new Promise((resolve, reject) => {
      const timeoutMs = options?.timeout || 5000
      const timeout = setTimeout(() => {
        this.pendingRequests.delete(id)
        reject(new Error(`Message timeout after ${timeoutMs}ms: ${payload.type}`))
      }, timeoutMs)

      this.pendingRequests.set(id, {
        resolve: (value) => {
          clearTimeout(timeout)
          resolve(value)
        },
        reject: (error) => {
          clearTimeout(timeout)
          reject(error)
        },
        timestamp: Date.now(),
        timeout
      })

      // Send via appropriate channel
      this.sendMessage(message)
    })
  }

  /**
   * Broadcast message to all contexts.
   * Used for state synchronization.
   */
  broadcast<T extends ExtensionMessage>(payload: T): void {
    const message: RoutedMessage<T> = {
      id: crypto.randomUUID(),
      source: this.context,
      target: 'broadcast',
      timestamp: Date.now(),
      payload
    }

    this.sendMessage(message)
  }

  /**
   * Register a typed message handler.
   * Handler signature is enforced based on message type.
   */
  on<T extends ExtensionMessage['type']>(
    type: T,
    handler: (
      payload: Extract<ExtensionMessage, { type: T }>,
      message: RoutedMessage<Extract<ExtensionMessage, { type: T }>>
    ) => Promise<MessageResponse<Extract<ExtensionMessage, { type: T }>>> | MessageResponse<Extract<ExtensionMessage, { type: T }>>
  ): void {
    this.handlers.set(type, handler as Handler)
  }

  /**
   * Connect with long-lived port.
   * Used for persistent connections (DevTools, Content Scripts).
   */
  connect(name: string): void {
    if (this.port) {
      console.warn(`Port already connected: ${this.port.name}`)
      return
    }

    this.port = this.adapters.runtime.connect(name)

    this.port.onMessage((message: RoutedMessage | RoutedResponse) => {
      this.handleMessage(message)
    })

    this.port.onDisconnect(() => {
      console.warn(`Port disconnected: ${name}`)
      this.port = null

      // Reject all pending requests
      for (const [id, pending] of this.pendingRequests.entries()) {
        pending.reject(new Error('Port disconnected'))
        clearTimeout(pending.timeout)
        this.pendingRequests.delete(id)
      }
    })
  }

  /**
   * Disconnect port if connected.
   */
  disconnect(): void {
    if (this.port) {
      this.port.disconnect()
      this.port = null
    }
  }

  /**
   * Remove all handlers and clean up.
   */
  destroy(): void {
    this.disconnect()
    this.handlers.clear()

    // Clear all pending requests
    for (const pending of this.pendingRequests.values()) {
      clearTimeout(pending.timeout)
    }
    this.pendingRequests.clear()

    // Remove message listener
    if (this.messageListener) {
      // Clean up would depend on adapter implementation
    }
  }

  private setupListeners(): void {
    // Listen for one-off messages via chrome.runtime.sendMessage
    this.messageListener = (message: RoutedMessage | RoutedResponse, sender: any, sendResponse: any) => {
      this.handleMessage(message, sender).then(sendResponse).catch((error) => {
        sendResponse({ success: false, error: error.message })
      })
      return true // Indicates async response
    }
    this.adapters.runtime.onMessage(this.messageListener)

    // Content/Page script window messaging
    if (this.context === 'content' || this.context === 'page') {
      this.adapters.window.addEventListener('message', (event: MessageEvent) => {
        if (event.source !== window) return
        if (event.data?.__extensionMessage) {
          this.handleMessage(event.data.message)
        }
      })
    }
  }

  private async handleMessage(
    message: RoutedMessage | RoutedResponse,
    sender?: any
  ): Promise<any> {
    // Handle response to our request
    if ('success' in message) {
      const pending = this.pendingRequests.get(message.id)
      if (pending) {
        this.pendingRequests.delete(message.id)
        clearTimeout(pending.timeout)

        if (message.success) {
          pending.resolve(message.data)
        } else {
          pending.reject(new Error(message.error || 'Unknown error'))
        }
      }
      return
    }

    // Ignore messages not targeted at us (unless broadcast)
    if (message.target !== this.context && message.target !== 'broadcast') {
      // If we're background, we need to route it
      if (this.context === 'background') {
        return // Routing handled elsewhere
      }
      return
    }

    // Handle incoming request
    const handler = this.handlers.get(message.payload.type)
    if (!handler) {
      if (message.target !== 'broadcast') {
        console.warn(`[${this.context}] No handler for message type: ${message.payload.type}`)
      }
      return { success: false, error: 'No handler' }
    }

    try {
      const data = await handler(message.payload, message)
      const response: RoutedResponse = {
        id: message.id,
        success: true,
        data,
        timestamp: Date.now()
      }

      // Send response back (only if not broadcast)
      if (message.target !== 'broadcast') {
        this.sendResponse(message, response)
      }

      return response
    } catch (error) {
      const response: RoutedResponse = {
        id: message.id,
        success: false,
        error: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      }

      if (message.target !== 'broadcast') {
        this.sendResponse(message, response)
      }

      return response
    }
  }

  private sendMessage(message: RoutedMessage): void {
    if (this.context === 'content' && message.target === 'page') {
      // Content → Page via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, '*')
    } else if (this.context === 'page') {
      // Page → Content via window.postMessage
      this.adapters.window.postMessage({ __extensionMessage: true, message }, '*')
    } else if (this.port && (this.context === 'devtools' || this.context === 'content')) {
      // Use long-lived port if connected
      this.port.postMessage(message)
    } else {
      // Use chrome.runtime.sendMessage
      this.adapters.runtime.sendMessage(message)
    }
  }

  private sendResponse(request: RoutedMessage, response: RoutedResponse): void {
    if (this.context === 'content' && request.source === 'page') {
      // Content → Page response
      this.adapters.window.postMessage({ __extensionMessage: true, message: response }, '*')
    } else if (this.context === 'page' && request.source === 'content') {
      // Page → Content response
      this.adapters.window.postMessage({ __extensionMessage: true, message: response }, '*')
    } else if (this.port && (this.context === 'devtools' || this.context === 'content')) {
      // Use port for response
      this.port.postMessage(response)
    } else {
      // Use chrome.runtime.sendMessage
      this.adapters.runtime.sendMessage(response)
    }
  }

  private inferTarget(type: ExtensionMessage['type']): Context {
    const handlers: Partial<MessageHandler> = {
      'DOM_QUERY': 'content',
      'DOM_UPDATE': 'content',
      'DOM_INSERT': 'content',
      'DOM_REMOVE': 'content',
      'PAGE_EVAL': 'page',
      'PAGE_GET_VAR': 'page',
      'PAGE_CALL_FN': 'page',
      'PAGE_SET_VAR': 'page',
      'API_REQUEST': 'background',
      'API_BATCH': 'background',
      'CLIPBOARD_WRITE': 'offscreen',
      'CLIPBOARD_WRITE_HTML': 'offscreen',
      'CLIPBOARD_WRITE_RICH': 'offscreen',
      'CLIPBOARD_READ': 'offscreen',
      'CONTEXT_MENU_CREATE': 'background',
      'CONTEXT_MENU_REMOVE': 'background',
      'TAB_QUERY': 'background',
      'TAB_GET_CURRENT': 'background',
      'TAB_RELOAD': 'background',
    }

    return handlers[type as keyof MessageHandler] || 'background'
  }
}

// Singleton instances per context
const messageBusInstances = new Map<Context, MessageBus>()

export function getMessageBus(context: Context, adapters?: ExtensionAdapters): MessageBus {
  if (!messageBusInstances.has(context)) {
    messageBusInstances.set(context, new MessageBus(context, adapters))
  }
  return messageBusInstances.get(context)!
}

export function destroyMessageBus(context: Context): void {
  const bus = messageBusInstances.get(context)
  if (bus) {
    bus.destroy()
    messageBusInstances.delete(context)
  }
}
```

## Usage Examples

### Example 1: DevTools queries DOM

```typescript
// devtools/panel.tsx
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('devtools')
const tabId = chrome.devtools.inspectedWindow.tabId

async function queryElements() {
  // Type-safe send - response type automatically inferred!
  const response = await bus.send(
    { type: 'DOM_QUERY', selector: '.data-item' },
    { tabId }
  )

  // response is typed as: { elements: Array<{ tag, text, html, attrs, rect? }> }
  console.log('Found elements:', response.elements)

  for (const element of response.elements) {
    console.log(`<${element.tag}>: ${element.text}`)
  }
}
```

### Example 2: Background handles API requests

```typescript
// background/index.ts
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('background')

// Register handler for API requests
bus.on('API_REQUEST', async (payload) => {
  // payload is typed as: { type: 'API_REQUEST'; endpoint: string; method: ...; body?: ...; headers?: ... }

  const { endpoint, method, body, headers } = payload

  try {
    const response = await fetch(endpoint, {
      method,
      headers: {
        'Content-Type': 'application/json',
        ...headers
      },
      body: body ? JSON.stringify(body) : undefined
    })

    const data = await response.json()

    // Return must match MessageResponse<{ type: 'API_REQUEST' }>
    return {
      data,
      status: response.status,
      statusText: response.statusText,
      headers: Object.fromEntries(response.headers.entries())
    }
  } catch (error) {
    return {
      data: null,
      status: 0,
      statusText: 'Network Error',
      headers: {},
      error: error instanceof Error ? error.message : 'Unknown error'
    }
  }
})
```

### Example 3: Offscreen handles clipboard

```typescript
// offscreen/index.ts
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('offscreen')

bus.on('CLIPBOARD_WRITE', async (payload) => {
  await navigator.clipboard.writeText(payload.text)
  return { success: true }
})

bus.on('CLIPBOARD_WRITE_HTML', async (payload) => {
  const blob = new Blob([payload.html], { type: 'text/html' })
  const item = new ClipboardItem({ 'text/html': blob })
  await navigator.clipboard.write([item])
  return { success: true }
})

bus.on('CLIPBOARD_WRITE_RICH', async (payload) => {
  const textBlob = new Blob([payload.data.text], { type: 'text/plain' })
  const htmlBlob = new Blob([payload.data.html], { type: 'text/html' })
  const item = new ClipboardItem({
    'text/plain': textBlob,
    'text/html': htmlBlob
  })
  await navigator.clipboard.write([item])
  return { success: true }
})

bus.on('CLIPBOARD_READ', async () => {
  const text = await navigator.clipboard.readText()
  return { text }
})
```

### Example 4: Content Script handles DOM operations

```typescript
// content/index.ts
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('content')

// Connect with long-lived port
bus.connect('content-script')

bus.on('DOM_QUERY', async (payload) => {
  const elements = Array.from(document.querySelectorAll(payload.selector))

  return {
    elements: elements.map(el => ({
      tag: el.tagName.toLowerCase(),
      text: el.textContent || '',
      html: el.innerHTML,
      attrs: Object.fromEntries(
        Array.from(el.attributes).map(a => [a.name, a.value])
      ),
      rect: el.getBoundingClientRect()
    }))
  }
})

bus.on('DOM_UPDATE', async (payload) => {
  const el = document.querySelector(payload.selector)
  if (el) {
    el.textContent = payload.content
    return { success: true }
  }
  return { success: false }
})

bus.on('DOM_INSERT', async (payload) => {
  const target = document.querySelector('body') || document.documentElement
  target.insertAdjacentHTML(payload.position, payload.html)
  return { success: true }
})

bus.on('DOM_REMOVE', async (payload) => {
  const elements = document.querySelectorAll(payload.selector)
  elements.forEach(el => el.remove())
  return { success: true, count: elements.length }
})
```

### Example 5: Page Script accesses page's JS

```typescript
// page/index.ts
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('page')

bus.on('PAGE_EVAL', async (payload) => {
  try {
    // Execute in page context
    const result = eval(payload.code)
    return { result }
  } catch (error) {
    return {
      result: null,
      error: error instanceof Error ? error.message : 'Eval error'
    }
  }
})

bus.on('PAGE_GET_VAR', async (payload) => {
  const value = (window as any)[payload.varName]
  return {
    value,
    exists: payload.varName in window
  }
})

bus.on('PAGE_CALL_FN', async (payload) => {
  try {
    const fn = (window as any)[payload.fnName]
    if (typeof fn !== 'function') {
      return { result: null, error: 'Not a function' }
    }
    const result = fn(...payload.args)
    return { result }
  } catch (error) {
    return {
      result: null,
      error: error instanceof Error ? error.message : 'Call error'
    }
  }
})

bus.on('PAGE_SET_VAR', async (payload) => {
  try {
    (window as any)[payload.varName] = payload.value
    return { success: true }
  } catch (error) {
    return { success: false }
  }
})
```

### Example 6: Broadcast state updates

```typescript
// Any context can broadcast
const bus = getMessageBus('popup')

// Update state and broadcast to all contexts
bus.broadcast({
  type: 'STATE_SYNC',
  path: 'user.settings',
  value: { theme: 'dark' },
  timestamp: Date.now()
})

// All contexts receive and can react
bus.on('STATE_SYNC', async (payload) => {
  console.log(`State updated: ${payload.path}`, payload.value)
  // Update local signals, UI, etc.
})
```

## Testing

### Mock Message Bus

```typescript
// tests/mocks/message-bus.mock.ts
import type { ExtensionMessage, MessageResponse } from '../../src/shared/types/messages'

export class MockMessageBus {
  public sentMessages: ExtensionMessage[] = []
  public handlers = new Map<string, Function>()

  async send<T extends ExtensionMessage>(
    payload: T
  ): Promise<MessageResponse<T>> {
    this.sentMessages.push(payload)

    // Return mock response based on type
    if (payload.type === 'DOM_QUERY') {
      return { elements: [] } as any
    }
    if (payload.type === 'API_REQUEST') {
      return { data: {}, status: 200, statusText: 'OK', headers: {} } as any
    }

    return undefined as any
  }

  broadcast<T extends ExtensionMessage>(payload: T): void {
    this.sentMessages.push(payload)
  }

  on(type: string, handler: Function): void {
    this.handlers.set(type, handler)
  }

  connect(name: string): void {}
  disconnect(): void {}
  destroy(): void {}
}
```

### Unit Test Example

```typescript
// tests/unit/devtools.test.ts
import { describe, test, expect, beforeEach } from 'bun:test'
import { MockMessageBus } from '../mocks/message-bus.mock'

describe('DevTools Panel', () => {
  let bus: MockMessageBus

  beforeEach(() => {
    bus = new MockMessageBus()
  })

  test('should query DOM elements', async () => {
    await bus.send({ type: 'DOM_QUERY', selector: '.foo' })

    expect(bus.sentMessages).toHaveLength(1)
    expect(bus.sentMessages[0]).toEqual({
      type: 'DOM_QUERY',
      selector: '.foo'
    })
  })
})
```

## Best Practices

### 1. Always Specify Tab ID for Per-Tab Contexts

```typescript
// ✅ Correct
await bus.send(
  { type: 'DOM_QUERY', selector: '.foo' },
  { tabId: chrome.devtools.inspectedWindow.tabId }
)

// ❌ Wrong - will fail to route
await bus.send({ type: 'DOM_QUERY', selector: '.foo' })
```

### 2. Use Long-Lived Ports for High-Frequency Communication

```typescript
// ✅ DevTools with persistent connection
const bus = getMessageBus('devtools')
bus.connect(`devtools-${tabId}`)

// ❌ One-off messages work but less efficient for high frequency
```

### 3. Handle Errors Gracefully

```typescript
try {
  const response = await bus.send({ type: 'API_REQUEST', endpoint: '/data', method: 'GET' })
  if (response.error) {
    console.error('API error:', response.error)
  }
} catch (error) {
  console.error('Message timeout or port disconnected:', error)
}
```

### 4. Clean Up on Unmount

```typescript
// Preact component
import { useEffect } from 'preact/hooks'

export function Panel() {
  useEffect(() => {
    const bus = getMessageBus('devtools')
    bus.connect('devtools')

    return () => {
      bus.disconnect()
    }
  }, [])
}
```

### 5. Type Assertions for Unknown Response Data

```typescript
const response = await bus.send({
  type: 'API_REQUEST',
  endpoint: '/users',
  method: 'GET'
})

// response.data is typed as 'unknown' - need to validate
if (isUserArray(response.data)) {
  // Now safely typed
  response.data.forEach(user => console.log(user.name))
}
```

## Performance Considerations

- Use long-lived ports for contexts that communicate frequently
- Broadcast only when necessary (selective sync for signals)
- Implement message queuing for burst scenarios
- Add timeout values appropriate for operation type
- Consider message size limits (chrome.runtime.sendMessage has ~64MB limit)

## Security Considerations

- Validate all message payloads at runtime (consider zod schemas)
- Check `event.source === window` for window.postMessage
- Never eval untrusted code from messages
- Sanitize HTML before DOM insertion
- Validate origins for external messages
