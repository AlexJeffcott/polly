# Adapter Pattern

## Overview

The adapter pattern provides a thin abstraction layer over browser APIs, enabling:
- **Testability**: Inject mock adapters for unit tests
- **Browser-agnostic**: Support multiple browsers with different implementations
- **Decoupling**: Core logic doesn't depend on Chrome-specific APIs
- **Traceability**: Add logging, metrics, and debugging in adapters

## Architecture

```
┌─────────────────────────────────────┐
│      Application Code               │
│  (MessageBus, Handlers, UI, etc.)   │
└──────────────┬──────────────────────┘
               │ uses interfaces
               ↓
┌─────────────────────────────────────┐
│         Adapter Interfaces          │
│  (RuntimeAdapter, StorageAdapter)   │
└──────────────┬──────────────────────┘
               │ implemented by
     ┌─────────┴─────────┐
     ↓                   ↓
┌─────────────┐    ┌─────────────┐
│   Chrome    │    │    Mock     │
│Implementation│   │Implementation│
└──────┬──────┘    └─────────────┘
       ↓
┌─────────────┐
│ Chrome APIs │
└─────────────┘
```

## Adapter Interfaces

### 1. Runtime Adapter

Wraps `chrome.runtime` APIs for messaging and extension lifecycle.

```typescript
// src/shared/adapters/runtime.adapter.ts

export interface RuntimeAdapter {
  /**
   * Send a one-off message to another context
   */
  sendMessage<T>(message: T): Promise<any>

  /**
   * Listen for one-off messages
   */
  onMessage(
    callback: (message: any, sender: MessageSender, sendResponse: (response: any) => void) => void
  ): void

  /**
   * Create a long-lived connection
   */
  connect(name: string): PortAdapter

  /**
   * Listen for incoming connections
   */
  onConnect(callback: (port: PortAdapter) => void): void

  /**
   * Get URL for extension resource
   */
  getURL(path: string): string

  /**
   * Get extension ID
   */
  getId(): string
}

export interface PortAdapter {
  /**
   * Port name
   */
  readonly name: string

  /**
   * Send message through port
   */
  postMessage(message: any): void

  /**
   * Listen for messages on port
   */
  onMessage(callback: (message: any) => void): void

  /**
   * Listen for disconnection
   */
  onDisconnect(callback: () => void): void

  /**
   * Disconnect port
   */
  disconnect(): void
}

export interface MessageSender {
  tab?: {
    id: number
    url: string
    title: string
  }
  frameId?: number
  url?: string
}
```

### 2. Storage Adapter

Wraps `chrome.storage` APIs for persistent data.

```typescript
// src/shared/adapters/storage.adapter.ts

export interface StorageAdapter {
  /**
   * Get items from storage
   */
  get<T = Record<string, any>>(keys: string | string[] | null): Promise<T>

  /**
   * Set items in storage
   */
  set(items: Record<string, any>): Promise<void>

  /**
   * Remove items from storage
   */
  remove(keys: string | string[]): Promise<void>

  /**
   * Clear all storage
   */
  clear(): Promise<void>

  /**
   * Listen for storage changes
   */
  onChanged(
    callback: (changes: StorageChanges, areaName: string) => void
  ): void
}

export interface StorageChanges {
  [key: string]: {
    oldValue?: any
    newValue?: any
  }
}
```

### 3. Tabs Adapter

Wraps `chrome.tabs` APIs for tab management.

```typescript
// src/shared/adapters/tabs.adapter.ts

export interface TabsAdapter {
  /**
   * Query tabs
   */
  query(queryInfo: TabQueryInfo): Promise<Tab[]>

  /**
   * Get tab by ID
   */
  get(tabId: number): Promise<Tab>

  /**
   * Send message to specific tab
   */
  sendMessage(tabId: number, message: any): Promise<any>

  /**
   * Reload tab
   */
  reload(tabId: number, reloadProperties?: { bypassCache?: boolean }): Promise<void>

  /**
   * Listen for tab removal
   */
  onRemoved(callback: (tabId: number, removeInfo: any) => void): void

  /**
   * Listen for tab updates
   */
  onUpdated(callback: (tabId: number, changeInfo: any, tab: Tab) => void): void

  /**
   * Listen for tab activation
   */
  onActivated(callback: (activeInfo: { tabId: number; windowId: number }) => void): void
}

export interface Tab {
  id?: number
  url?: string
  title?: string
  active?: boolean
  windowId?: number
}

export interface TabQueryInfo {
  active?: boolean
  currentWindow?: boolean
  url?: string | string[]
  title?: string
}
```

### 4. Window Adapter

Wraps browser `window` APIs for content/page script communication.

```typescript
// src/shared/adapters/window.adapter.ts

export interface WindowAdapter {
  /**
   * Post message to window
   */
  postMessage(message: any, targetOrigin: string): void

  /**
   * Listen for messages
   */
  addEventListener(type: 'message', listener: (event: MessageEvent) => void): void

  /**
   * Remove message listener
   */
  removeEventListener(type: 'message', listener: (event: MessageEvent) => void): void
}

export interface MessageEvent {
  data: any
  origin: string
  source: Window | null
}
```

### 5. Offscreen Adapter

Wraps `chrome.offscreen` APIs for offscreen documents.

```typescript
// src/shared/adapters/offscreen.adapter.ts

export interface OffscreenAdapter {
  /**
   * Create offscreen document
   */
  createDocument(parameters: CreateOffscreenDocumentParameters): Promise<void>

  /**
   * Close offscreen document
   */
  closeDocument(): Promise<void>

  /**
   * Check if offscreen document exists
   */
  hasDocument(): Promise<boolean>
}

export interface CreateOffscreenDocumentParameters {
  url: string
  reasons: OffscreenReason[]
  justification: string
}

export type OffscreenReason =
  | 'AUDIO_PLAYBACK'
  | 'BLOBS'
  | 'CLIPBOARD'
  | 'DOM_PARSER'
  | 'DOM_SCRAPING'
  | 'IFRAME_SCRIPTING'
  | 'LOCAL_STORAGE'
  | 'MATCH_MEDIA'
  | 'TESTING'
  | 'USER_MEDIA'
  | 'WEB_RTC'
  | 'WORKERS'
```

### 6. Context Menus Adapter

Wraps `chrome.contextMenus` APIs.

```typescript
// src/shared/adapters/context-menus.adapter.ts

export interface ContextMenusAdapter {
  /**
   * Create context menu item
   */
  create(createProperties: ContextMenuCreateProperties): Promise<void>

  /**
   * Update context menu item
   */
  update(id: string, updateProperties: Partial<ContextMenuCreateProperties>): Promise<void>

  /**
   * Remove context menu item
   */
  remove(id: string): Promise<void>

  /**
   * Remove all context menu items
   */
  removeAll(): Promise<void>

  /**
   * Listen for context menu clicks
   */
  onClicked(
    callback: (info: OnClickData, tab?: Tab) => void
  ): void
}

export interface ContextMenuCreateProperties {
  id: string
  title: string
  contexts: ContextType[]
  visible?: boolean
  enabled?: boolean
  parentId?: string
}

export type ContextType =
  | 'all'
  | 'page'
  | 'frame'
  | 'selection'
  | 'link'
  | 'editable'
  | 'image'
  | 'video'
  | 'audio'

export interface OnClickData {
  menuItemId: string
  parentMenuItemId?: string
  mediaType?: string
  linkUrl?: string
  srcUrl?: string
  pageUrl?: string
  frameUrl?: string
  selectionText?: string
  editable: boolean
}
```

### 7. Fetch Adapter

Wraps the `fetch` API for consistent HTTP requests and testability.

```typescript
// src/shared/adapters/fetch.adapter.ts

export interface FetchAdapter {
  /**
   * Perform an HTTP request
   */
  fetch(input: string | URL, init?: RequestInit): Promise<Response>
}
```

**Why Fetch Needs an Adapter:**

While `fetch` is a browser API, wrapping it provides:
- **Testability**: Mock HTTP responses in tests
- **Consistency**: All external APIs go through adapters
- **Extensibility**: Add retry logic, logging, or caching in one place

**Chrome Implementation:**

```typescript
// src/shared/adapters/chrome/fetch.chrome.ts

export class BrowserFetchAdapter implements FetchAdapter {
  fetch(input: string | URL, init?: RequestInit): Promise<Response> {
    return fetch(input, init)
  }
}
```

**Usage in Services:**

```typescript
// src/background/api-client.ts

export class ApiClient {
  private bus: MessageBus

  constructor(bus?: MessageBus) {
    this.bus = bus || getMessageBus('background')
    this.setupHandlers()
  }

  private setupHandlers(): void {
    this.bus.on('API_REQUEST', async (payload) => {
      const { endpoint, method, body, headers } = payload

      try {
        // Use fetch adapter from MessageBus
        const response = await this.bus.adapters.fetch.fetch(endpoint, {
          method,
          headers: {
            'Content-Type': 'application/json',
            ...headers,
          },
          body: body ? JSON.stringify(body) : undefined,
        })

        const data = response.ok ? await response.json() : null

        return {
          status: response.status,
          statusText: response.statusText,
          data,
        }
      } catch (error) {
        return {
          status: 0,
          error: error instanceof Error ? error.message : 'Unknown error',
        }
      }
    })
  }
}
```

### 8. Logger Adapter

Wraps logging output for consistent, testable logging across all contexts. Uses **message-based centralized architecture** where logs are sent to a LogStore service in the background.

```typescript
// src/shared/adapters/logger.adapter.ts

export interface LoggerAdapter {
  /**
   * Debug-level logging (verbose)
   */
  debug(message: string, context?: Record<string, unknown>): void

  /**
   * Info-level logging
   */
  info(message: string, context?: Record<string, unknown>): void

  /**
   * Warning-level logging
   */
  warn(message: string, context?: Record<string, unknown>): void

  /**
   * Error-level logging
   */
  error(message: string, error?: Error, context?: Record<string, unknown>): void

  /**
   * Log with explicit level
   */
  log(level: LogLevel, message: string, context?: Record<string, unknown>): void
}

export type LogLevel = 'debug' | 'info' | 'warn' | 'error'
```

**Why Logging Needs an Adapter:**

- **Testability**: Mock logger can capture or silence calls
- **Centralized**: All logs stored in background LogStore with filtering/export
- **Consistency**: All external output goes through adapters
- **Flexibility**: Switch implementations without changing code
- **No Environment Detection**: Just inject different adapters (production vs test)

**Production Implementation:**

```typescript
// src/shared/adapters/logger.adapter.ts

export class MessageLoggerAdapter implements LoggerAdapter {
  constructor(
    private runtime: RuntimeAdapter,
    private sourceContext: Context,
    private options?: MessageLoggerOptions
  ) {}

  debug(message: string, context?: Record<string, unknown>): void {
    this.sendLog('debug', message, context)
  }

  info(message: string, context?: Record<string, unknown>): void {
    this.sendLog('info', message, context)
  }

  warn(message: string, context?: Record<string, unknown>): void {
    this.sendLog('warn', message, context)
  }

  error(message: string, error?: Error, context?: Record<string, unknown>): void {
    this.sendLog('error', message, context, error)
  }

  log(level: LogLevel, message: string, context?: Record<string, unknown>): void {
    this.sendLog(level, message, context)
  }

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

**Usage:**

```typescript
// Access through MessageBus adapters
this.bus.adapters.logger.debug('Port connected', { port: port.name })
this.bus.adapters.logger.error('Request failed', error, { endpoint })
```

See [LOGGING.md](./LOGGING.md) for comprehensive logging guide with filtering, export, and querying.

## Chrome Implementations

### 1. Chrome Runtime Adapter

```typescript
// src/shared/adapters/chrome/runtime.chrome.ts

import type { RuntimeAdapter, PortAdapter, MessageSender } from '../runtime.adapter'

export class ChromeRuntimeAdapter implements RuntimeAdapter {
  sendMessage<T>(message: T): Promise<any> {
    return chrome.runtime.sendMessage(message)
  }

  onMessage(
    callback: (message: any, sender: MessageSender, sendResponse: (response: any) => void) => void
  ): void {
    chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
      const mappedSender: MessageSender = {
        tab: sender.tab ? {
          id: sender.tab.id!,
          url: sender.tab.url!,
          title: sender.tab.title!
        } : undefined,
        frameId: sender.frameId,
        url: sender.url
      }
      callback(message, mappedSender, sendResponse)
    })
  }

  connect(name: string): PortAdapter {
    const port = chrome.runtime.connect({ name })
    return new ChromePortAdapter(port)
  }

  onConnect(callback: (port: PortAdapter) => void): void {
    chrome.runtime.onConnect.addListener((port) => {
      callback(new ChromePortAdapter(port))
    })
  }

  getURL(path: string): string {
    return chrome.runtime.getURL(path)
  }

  getId(): string {
    return chrome.runtime.id
  }
}

class ChromePortAdapter implements PortAdapter {
  private listeners = {
    message: new Set<(message: any) => void>(),
    disconnect: new Set<() => void>()
  }

  constructor(private port: chrome.runtime.Port) {
    // Set up Chrome port listeners
    this.port.onMessage.addListener((message) => {
      this.listeners.message.forEach(callback => callback(message))
    })

    this.port.onDisconnect.addListener(() => {
      this.listeners.disconnect.forEach(callback => callback())
    })
  }

  get name(): string {
    return this.port.name
  }

  postMessage(message: any): void {
    this.port.postMessage(message)
  }

  onMessage(callback: (message: any) => void): void {
    this.listeners.message.add(callback)
  }

  onDisconnect(callback: () => void): void {
    this.listeners.disconnect.add(callback)
  }

  disconnect(): void {
    this.port.disconnect()
  }
}
```

### 2. Chrome Storage Adapter

```typescript
// src/shared/adapters/chrome/storage.chrome.ts

import type { StorageAdapter, StorageChanges } from '../storage.adapter'

export class ChromeStorageAdapter implements StorageAdapter {
  async get<T = Record<string, any>>(keys: string | string[] | null): Promise<T> {
    return chrome.storage.local.get(keys) as Promise<T>
  }

  async set(items: Record<string, any>): Promise<void> {
    await chrome.storage.local.set(items)
  }

  async remove(keys: string | string[]): Promise<void> {
    await chrome.storage.local.remove(keys)
  }

  async clear(): Promise<void> {
    await chrome.storage.local.clear()
  }

  onChanged(callback: (changes: StorageChanges, areaName: string) => void): void {
    chrome.storage.onChanged.addListener((changes, areaName) => {
      const mappedChanges: StorageChanges = {}
      for (const [key, change] of Object.entries(changes)) {
        mappedChanges[key] = {
          oldValue: change.oldValue,
          newValue: change.newValue
        }
      }
      callback(mappedChanges, areaName)
    })
  }
}
```

### 3. Chrome Tabs Adapter

```typescript
// src/shared/adapters/chrome/tabs.chrome.ts

import type { TabsAdapter, Tab, TabQueryInfo } from '../tabs.adapter'

export class ChromeTabsAdapter implements TabsAdapter {
  async query(queryInfo: TabQueryInfo): Promise<Tab[]> {
    return chrome.tabs.query(queryInfo as chrome.tabs.QueryInfo)
  }

  async get(tabId: number): Promise<Tab> {
    return chrome.tabs.get(tabId)
  }

  async sendMessage(tabId: number, message: any): Promise<any> {
    return chrome.tabs.sendMessage(tabId, message)
  }

  async reload(tabId: number, reloadProperties?: { bypassCache?: boolean }): Promise<void> {
    await chrome.tabs.reload(tabId, reloadProperties)
  }

  onRemoved(callback: (tabId: number, removeInfo: any) => void): void {
    chrome.tabs.onRemoved.addListener(callback)
  }

  onUpdated(callback: (tabId: number, changeInfo: any, tab: Tab) => void): void {
    chrome.tabs.onUpdated.addListener(callback)
  }

  onActivated(callback: (activeInfo: { tabId: number; windowId: number }) => void): void {
    chrome.tabs.onActivated.addListener(callback)
  }
}
```

### 4. Chrome Window Adapter

```typescript
// src/shared/adapters/chrome/window.chrome.ts

import type { WindowAdapter } from '../window.adapter'

export class ChromeWindowAdapter implements WindowAdapter {
  postMessage(message: any, targetOrigin: string): void {
    window.postMessage(message, targetOrigin)
  }

  addEventListener(type: 'message', listener: (event: MessageEvent) => void): void {
    window.addEventListener(type, listener as any)
  }

  removeEventListener(type: 'message', listener: (event: MessageEvent) => void): void {
    window.removeEventListener(type, listener as any)
  }
}
```

### 5. Chrome Offscreen Adapter

```typescript
// src/shared/adapters/chrome/offscreen.chrome.ts

import type { OffscreenAdapter, CreateOffscreenDocumentParameters } from '../offscreen.adapter'

export class ChromeOffscreenAdapter implements OffscreenAdapter {
  async createDocument(parameters: CreateOffscreenDocumentParameters): Promise<void> {
    await chrome.offscreen.createDocument({
      url: parameters.url,
      reasons: parameters.reasons as chrome.offscreen.Reason[],
      justification: parameters.justification
    })
  }

  async closeDocument(): Promise<void> {
    await chrome.offscreen.closeDocument()
  }

  async hasDocument(): Promise<boolean> {
    // Chrome doesn't provide a direct API, so we try to query
    const offscreenUrl = chrome.runtime.getURL('offscreen/offscreen.html')
    const existingContexts = await chrome.runtime.getContexts({
      contextTypes: ['OFFSCREEN_DOCUMENT' as chrome.runtime.ContextType]
    })
    return existingContexts.length > 0
  }
}
```

### 6. Chrome Context Menus Adapter

```typescript
// src/shared/adapters/chrome/context-menus.chrome.ts

import type { ContextMenusAdapter, ContextMenuCreateProperties, OnClickData } from '../context-menus.adapter'
import type { Tab } from '../tabs.adapter'

export class ChromeContextMenusAdapter implements ContextMenusAdapter {
  async create(createProperties: ContextMenuCreateProperties): Promise<void> {
    return new Promise((resolve, reject) => {
      chrome.contextMenus.create({
        id: createProperties.id,
        title: createProperties.title,
        contexts: createProperties.contexts as chrome.contextMenus.ContextType[],
        visible: createProperties.visible,
        enabled: createProperties.enabled,
        parentId: createProperties.parentId
      }, () => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message))
        } else {
          resolve()
        }
      })
    })
  }

  async update(id: string, updateProperties: Partial<ContextMenuCreateProperties>): Promise<void> {
    await chrome.contextMenus.update(id, updateProperties as any)
  }

  async remove(id: string): Promise<void> {
    await chrome.contextMenus.remove(id)
  }

  async removeAll(): Promise<void> {
    await chrome.contextMenus.removeAll()
  }

  onClicked(callback: (info: OnClickData, tab?: Tab) => void): void {
    chrome.contextMenus.onClicked.addListener((info, tab) => {
      const mappedInfo: OnClickData = {
        menuItemId: info.menuItemId as string,
        parentMenuItemId: info.parentMenuItemId as string | undefined,
        mediaType: info.mediaType,
        linkUrl: info.linkUrl,
        srcUrl: info.srcUrl,
        pageUrl: info.pageUrl,
        frameUrl: info.frameUrl,
        selectionText: info.selectionText,
        editable: info.editable
      }
      callback(mappedInfo, tab)
    })
  }
}
```

## Adapter Factory

```typescript
// src/shared/adapters/index.ts

import { ChromeRuntimeAdapter } from './chrome/runtime.chrome'
import { ChromeStorageAdapter } from './chrome/storage.chrome'
import { ChromeTabsAdapter } from './chrome/tabs.chrome'
import { ChromeWindowAdapter } from './chrome/window.chrome'
import { ChromeOffscreenAdapter } from './chrome/offscreen.chrome'
import { ChromeContextMenusAdapter } from './chrome/context-menus.chrome'
import { BrowserFetchAdapter } from './chrome/fetch.chrome'
import { MessageLoggerAdapter } from './logger.adapter'

import type { RuntimeAdapter } from './runtime.adapter'
import type { StorageAdapter } from './storage.adapter'
import type { TabsAdapter } from './tabs.adapter'
import type { WindowAdapter } from './window.adapter'
import type { OffscreenAdapter } from './offscreen.adapter'
import type { ContextMenusAdapter } from './context-menus.adapter'
import type { FetchAdapter } from './fetch.adapter'
import type { LoggerAdapter } from './logger.adapter'
import type { Context } from './types/messages'

export interface ExtensionAdapters {
  runtime: RuntimeAdapter
  storage: StorageAdapter
  tabs: TabsAdapter
  window: WindowAdapter
  offscreen: OffscreenAdapter
  contextMenus: ContextMenusAdapter
  fetch: FetchAdapter
  logger: LoggerAdapter
}

export interface CreateChromeAdaptersOptions {
  consoleMirror?: boolean
  fallbackToConsole?: boolean
}

/**
 * Create Chrome-specific adapters
 * @param context - The context this adapter set is for (background, content, popup, etc.)
 * @param options - Optional configuration for adapters
 */
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
    // Logger uses RuntimeAdapter to send LOG messages to background
    logger: new MessageLoggerAdapter(runtime, context, {
      consoleMirror: options?.consoleMirror,
      fallbackToConsole: options?.fallbackToConsole ?? true,
    }),
  }
}

// Re-export types
export * from './runtime.adapter'
export * from './storage.adapter'
export * from './tabs.adapter'
export * from './window.adapter'
export * from './offscreen.adapter'
export * from './context-menus.adapter'
export * from './fetch.adapter'
export * from './logger.adapter'
```

## Mock Adapters for Testing

Mock adapters live in `tests/helpers/adapters/` and mirror the structure of `src/shared/adapters/`.

**Key Principles:**
- Mock interfaces **extend** production adapter interfaces
- Add internal test helpers with `_` prefix (e.g., `_connectListeners`)
- Use factory functions instead of classes for simplicity
- Support both isolated and integrated testing patterns

### Mock Structure

```
tests/helpers/adapters/
├── index.ts              # Main exports with createMockAdapters()
├── runtime.mock.ts       # MockRuntime extends RuntimeAdapter
├── storage.mock.ts       # MockStorageArea extends StorageAdapter
├── tabs.mock.ts          # MockTabs extends TabsAdapter
├── window.mock.ts        # MockWindow extends WindowAdapter
├── offscreen.mock.ts     # MockOffscreen extends OffscreenAdapter
├── context-menus.mock.ts # MockContextMenus extends ContextMenusAdapter
├── fetch.mock.ts         # MockFetch extends FetchAdapter
└── logger.mock.ts        # MockLogger extends LoggerAdapter
```

### Example: Mock Runtime Adapter

```typescript
// tests/helpers/adapters/runtime.mock.ts

import type { RuntimeAdapter, PortAdapter, MessageSender } from '@/shared/adapters/runtime.adapter'

export interface MockRuntime extends RuntimeAdapter {
  _connectListeners: Array<(port: PortAdapter) => void>
  _messageListeners: Array<(message: any, sender: any, sendResponse: any) => void>
}

export function createMockRuntime(): MockRuntime {
  const connectListeners: Array<(port: PortAdapter) => void> = []
  const messageListeners: Array<(message: any, sender: any, sendResponse: any) => void> = []

  return {
    sendMessage: async <T>(message: T): Promise<any> => {
      // Simulate sending - actual behavior in tests
      return { success: true }
    },

    onMessage(callback) {
      messageListeners.push(callback)
    },

    connect(name: string): PortAdapter {
      return createMockPort(name)
    },

    onConnect(callback) {
      connectListeners.push(callback)
    },

    getURL(path: string): string {
      return `chrome-extension://test-extension-id/${path}`
    },

    getId(): string {
      return 'test-extension-id'
    },

    // Test-only internals
    _connectListeners: connectListeners,
    _messageListeners: messageListeners,
  }
}
```

### Example: Mock Fetch Adapter

```typescript
// tests/helpers/adapters/fetch.mock.ts

import type { FetchAdapter } from '@/shared/adapters/fetch.adapter'

export interface MockFetch extends FetchAdapter {
  _responses: Array<Partial<Response>>
  _calls: Array<{ input: string | URL; init?: RequestInit }>
}

export function createMockFetch(): MockFetch {
  const responses: Array<Partial<Response>> = []
  const calls: Array<{ input: string | URL; init?: RequestInit }> = []

  const defaultResponse: Partial<Response> = {
    ok: true,
    status: 200,
    headers: new Headers(),
    statusText: 'OK',
    json: async () => ({}),
  }

  return {
    fetch: async (input: string | URL, init?: RequestInit): Promise<Response> => {
      calls.push({ input, init })
      const mockResponse = responses.shift() || defaultResponse
      return mockResponse as Response
    },
    _responses: responses,
    _calls: calls,
  }
}
```

### Example: Mock Logger Adapter

```typescript
// tests/helpers/adapters/logger.mock.ts

import type { LoggerAdapter, LogLevel } from '@/shared/adapters/logger.adapter'

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

  const logToConsole = (level: LogLevel, message: string, context?: Record<string, unknown>) => {
    if (!silent) {
      console[level](message, context)
    }
  }

  return {
    debug(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'debug', message, context, timestamp: Date.now() })
      logToConsole('debug', message, context)
    },

    info(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'info', message, context, timestamp: Date.now() })
      logToConsole('info', message, context)
    },

    warn(message: string, context?: Record<string, unknown>): void {
      calls.push({ level: 'warn', message, context, timestamp: Date.now() })
      logToConsole('warn', message, context)
    },

    error(message: string, error?: Error, context?: Record<string, unknown>): void {
      calls.push({ level: 'error', message, error, context, timestamp: Date.now() })
      logToConsole('error', message, { ...context, error })
    },

    log(level: LogLevel, message: string, context?: Record<string, unknown>): void {
      calls.push({ level, message, context, timestamp: Date.now() })
      logToConsole(level, message, context)
    },

    // Test-only internals
    _calls: calls,
    _clear() {
      calls.length = 0
    },
  }
}
```

**Key Features:**
- **Captures calls**: All log calls stored in `_calls` array for assertions
- **Silent by default**: No console output (set `silent: false` for debugging)
- **Clearable**: Use `_clear()` to reset between tests
- **No message sending**: Unlike MessageLoggerAdapter, doesn't send LOG messages

### Using Mock Adapters

**Simple usage with `createMockAdapters()`:**

```typescript
import { createMockAdapters } from '../helpers/adapters'
import { MessageBus } from '@/shared/lib/message-bus'

test('Simple test', () => {
  const adapters = createMockAdapters()
  const bus = new MessageBus('background', adapters)
  // Use bus normally
})
```

**Advanced usage with mock internals:**

```typescript
import {
  createMockRuntime,
  createMockStorageArea,
  createMockFetch,
  createMockLogger,
  type MockRuntime,
  type MockFetch,
  type MockLogger,
} from '../helpers/adapters'
import type { ExtensionAdapters } from '@/shared/adapters'

test('Advanced test', async () => {
  // Create mocks you need separately
  const mockRuntime = createMockRuntime()
  const mockFetch = createMockFetch()
  const mockLogger = createMockLogger()

  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: mockFetch,
    logger: mockLogger,
  }

  // Access mock internals
  mockFetch._responses.push({
    ok: true,
    status: 200,
    json: async () => ({ data: 'test' }),
  })

  mockRuntime._connectListeners.forEach(listener => {
    listener(port)
  })

  // Assert on fetch calls
  expect(mockFetch._calls).toHaveLength(1)

  // Assert on log calls
  expect(mockLogger._calls).toHaveLength(2)
  expect(mockLogger._calls[0].level).toBe('info')
})
```

For comprehensive testing patterns and examples, see [TESTING.md](./TESTING.md).

## Dependency Injection Pattern

All services that use adapters should support dependency injection for testability:

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

// Production usage
const client = new ApiClient()  // Uses global bus

// Test usage
const mockBus = new MessageBus('background', mockAdapters)
const client = new ApiClient(mockBus)  // Uses test bus
```

## Extending Adapters

### Logging Adapter (Decorator Pattern)

Wrap adapters with logging for debugging:

```typescript
export class LoggingRuntimeAdapter implements RuntimeAdapter {
  constructor(private inner: RuntimeAdapter) {}

  async sendMessage<T>(message: T): Promise<any> {
    console.log('Sending message:', message)
    const response = await this.inner.sendMessage(message)
    console.log('Received response:', response)
    return response
  }

  // ... delegate other methods
}
```

### Migration Path
Easy to switch between implementations:

```typescript
// Development: Use logging adapter
const adapters = createChromeAdapters()
const loggingAdapters = wrapWithLogging(adapters)

// Testing: Use mocks
const testAdapters = createMockAdapters()

// Production: Use Chrome directly
const prodAdapters = createChromeAdapters()
```

## Best Practices

1. **Always use adapters** - Never call Chrome APIs directly from application code
2. **Inject adapters** - Pass adapters to constructors (dependency injection)
3. **Mock for tests** - Use mock adapters for all unit tests
4. **Log through adapter** - Use `logger` adapter instead of `console.*` for testable logging
5. **Keep adapters thin** - No business logic in adapters, just API wrapping
6. **Use path aliases** - Import with `@/` instead of relative paths
7. **Extend, don't modify** - Mock interfaces extend production interfaces
8. **Factory functions** - Use factory functions for mocks (`createMockRuntime()`)
9. **Test internals with `_` prefix** - Mark test-only members clearly
10. **Lazy initialization** - Defer chrome API calls until runtime (not module load)

## See Also

- [TESTING.md](./TESTING.md) - Comprehensive testing patterns and examples
- [LOGGING.md](./LOGGING.md) - Logger adapter usage and patterns
- [ERRORS.md](./ERRORS.md) - Type-safe error handling system
- [MESSAGING.md](./MESSAGING.md) - Message bus architecture
- [ARCHITECTURE.md](./ARCHITECTURE.md) - Overall system design
