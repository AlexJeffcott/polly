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
  DOM_QUERY: "content";
  DOM_UPDATE: "content";
  DOM_INSERT: "content";
  DOM_REMOVE: "content";

  PAGE_GET_VAR: "page";
  PAGE_CALL_FN: "page";
  PAGE_SET_VAR: "page";

  API_REQUEST: "background";
  API_BATCH: "background";

  CLIPBOARD_WRITE: "offscreen";
  CLIPBOARD_WRITE_HTML: "offscreen";
  CLIPBOARD_WRITE_RICH: "offscreen";
  CLIPBOARD_READ: "offscreen";

  CONTEXT_MENU_CLICKED: "background";
  CONTEXT_MENU_CREATE: "background";
  CONTEXT_MENU_REMOVE: "background";

  STATE_SYNC: Context[]; // Broadcast to every listed context

  TAB_QUERY: "background";
  TAB_GET_CURRENT: "background";
  TAB_RELOAD: "background";

  DEVTOOLS_INSPECT_ELEMENT: "content";
  DEVTOOLS_LOG: "background";

  LOG: "background";
  LOGS_GET: "background";
  LOGS_CLEAR: "background";
  LOGS_EXPORT: "background";
};

export type Context =
  | "background"
  | "content"
  | "page"
  | "devtools"
  | "popup"
  | "options"
  | "offscreen";
```

Each value is either a single `Context` literal or an array of
contexts. There is no `"broadcast"` literal — broadcasting is modelled
as a `Context[]` listing every context that should receive the
message. `STATE_SYNC` is the canonical example.

### 4. Routed Message Envelope

Every message is wrapped in a routing envelope:

```typescript
export type RoutedMessage<T extends BaseMessage = ExtensionMessage> = {
  id: string;          // Correlation ID (UUID)
  source: Context;     // Which context sent it
  targets: Context[];  // Which contexts should receive it (one entry, or several)
  tabId?: number;      // Required for per-tab contexts (content, page, devtools)
  timestamp: number;   // When it was sent
  payload: T;          // The actual message
};

export type RoutedResponse<T extends BaseMessage = ExtensionMessage> = {
  id: string;                  // Matches the request id
  success: boolean;            // Whether the handler succeeded
  data?: MessageResponse<T>;   // Typed response payload
  error?: string;              // Error message if failed
  timestamp: number;           // When response was sent
};
```

`targets` is an array on the envelope: a unicast send produces a
one-element array, a broadcast produces several. The type parameter is
`BaseMessage` (the minimal contract — just a `type` field) so consumers
can use these envelopes with their own message union, not only
`ExtensionMessage`.

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

## MessageBus implementation

The implementation lives at `src/shared/lib/message-bus.ts`. The salient
details:

- `class MessageBus<TMessage extends BaseMessage = ExtensionMessage>`. The
  default type parameter is the framework's `ExtensionMessage` union; a
  consumer application supplies its own union when its messages are not
  Polly built-ins.
- The bus holds an `ExtensionAdapters` value internally and exposes its
  adapters as `bus.adapters` for handlers that need to call into them
  directly (e.g. `bus.adapters.logger.info(...)`).
- `send(payload, options?)` wraps the payload in a `RoutedMessage`,
  generates a UUID `id`, attaches the local context as `source`, and
  resolves with the `RoutedResponse.data` of the first successful handler
  reply. Request timeouts surface as `TimeoutError` (default 5s, override
  with `options.timeoutMs`).
- `on(type, handler)` registers a handler for a single message type.
  Handlers are typed against `MessageHandlerMap[type]` so the handler's
  argument and return type are inferred from the message union.
- `destroy()` clears registered handlers, rejects pending requests with
  `ConnectionError`, and removes any listeners the bus installed on its
  adapters. There is no top-level `destroyMessageBus()` free function;
  call `bus.destroy()` on the instance you hold.
- `getMessageBus(context, adapters?)` returns the per-context singleton.
  Pass adapters explicitly to inject a mock stack in tests; omit them in
  production to use the default Chrome/web adapter set selected by
  `createChromeAdapters()`.

For the routing semantics — how messages cross the background script,
how broadcasts fan out, how per-tab targeting works — see the
implementation source. The bus is small (under 900 lines) and is the
authoritative description; this document does not duplicate it.

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

`STATE_SYNC` is the framework-internal channel the state primitives use to
propagate writes across contexts. Application code does not normally
emit it directly — `$sharedState`, `$syncedState`, etc. do — but the
shape is documented here for completeness:

```typescript
const bus = getMessageBus("popup");

bus.broadcast({
  type: "STATE_SYNC",
  key: "user.settings",
  value: { theme: "dark" },
  clock: lamport.next(),
});

bus.on("STATE_SYNC", async (payload) => {
  // payload is typed as { type: "STATE_SYNC"; key: string; value: unknown; clock: number }
  console.log(`State updated: ${payload.key}`, payload.value);
});
```

The Lamport `clock` is how concurrent writes from different contexts
are ordered; see [STATE.md](./STATE.md) for the full conflict-resolution
contract.

## Testing

Polly ships mock adapters for every adapter the bus uses, so tests
build a real `MessageBus` against fakes rather than mocking the bus
itself:

```typescript
import { describe, test, expect } from "bun:test";
import { MessageBus } from "@fairfox/polly/message-bus";
import { createMockAdapters } from "@fairfox/polly/test";

describe("DevTools panel", () => {
  test("queries the DOM via the runtime adapter", async () => {
    const adapters = createMockAdapters();
    const bus = new MessageBus("devtools", adapters);

    // Pre-seed a response for the runtime adapter to return.
    adapters.runtime._respondTo("DOM_QUERY", { elements: [] });

    const result = await bus.send({ type: "DOM_QUERY", selector: ".foo" });

    expect(result).toEqual({ elements: [] });
    expect(adapters.runtime._sentMessages).toHaveLength(1);
  });
});
```

The mocks live under `tools/test/src/adapters/`. They expose
inspection fields (`_sentMessages`, `_storage`, `_tabs`, etc.) and
helpers (`_respondTo`, `_emit`) — see
[TESTING.md](./TESTING.md) for the full surface. Writing a
hand-rolled `MockMessageBus` is unnecessary and not recommended.

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
