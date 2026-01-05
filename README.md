# @fairfox/polly

**Multi-execution-context framework with reactive state and cross-context messaging.**

Build Chrome extensions, PWAs, and worker-based applications with automatic state synchronization, reactive UI updates, and type-safe messaging.

## Why Polly?

Modern applications run code in multiple isolated execution contexts:

- **Chrome extensions**: Background service workers, popups, content scripts, options pages
- **PWAs**: Main thread, service workers, web workers
- **Node/Bun/Deno apps**: Main process, worker threads

Managing state and communication between these contexts is painful:

- ❌ State scattered across contexts with manual synchronization
- ❌ Complex message passing with serialization concerns
- ❌ No reactivity - manually update UI when state changes
- ❌ Difficult to test - must mock platform APIs
- ❌ Hard to reason about concurrent state updates

**Polly solves this:**

- ✅ **Reactive state** - UI updates automatically with Preact Signals
- ✅ **Auto-syncing** - State syncs across all contexts instantly with conflict resolution
- ✅ **Persistence** - Optional automatic persistence to chrome.storage or localStorage
- ✅ **Type-safe messaging** - Request/response pattern with full TypeScript support
- ✅ **Built for testing** - DOM-based E2E tests without mocking
- ✅ **Distributed consistency** - Lamport clocks prevent race conditions

## Installation

```bash
bun add @fairfox/polly preact @preact/signals
```

## Getting Started

### Example: PWA with Backend API

Let's build a PWA that connects to a backend API, with a service worker handling requests and the main thread rendering UI. Polly makes this trivial.

#### Step 1: Define Your Message Types

Create typed messages for communication between your UI and service worker:

```typescript
// src/shared/messages.ts
import type { ExtensionMessage } from '@fairfox/polly/types'

// Define your custom messages
type CustomMessages =
  | { type: 'API_FETCH_USER'; userId: string }
  | { type: 'API_UPDATE_USER'; userId: string; data: UserData }
  | { type: 'API_DELETE_USER'; userId: string }
  | { type: 'CACHE_CLEAR' }

// Combine with framework messages
export type AppMessages = ExtensionMessage | CustomMessages

export interface UserData {
  name: string
  email: string
  avatar: string
}
```

#### Step 2: Define Shared State

Create reactive state that automatically syncs across all contexts:

```typescript
// src/shared/state.ts
import { $sharedState, $syncedState, $state } from '@fairfox/polly/state'

// Synced + persisted (survives reload)
export const currentUser = $sharedState<UserData | null>('user', null)
export const settings = $sharedState('settings', {
  theme: 'dark' as 'light' | 'dark',
  notifications: true
})

// Synced but not persisted (temporary)
export const onlineStatus = $syncedState('online', true)
export const activeRequests = $syncedState('requests', 0)

// Local only (component state)
export const isLoading = $state(false)
```

**Why three types of state?**

- `$sharedState` - Use for user data, settings - anything that should persist
- `$syncedState` - Use for ephemeral shared state like connection status
- `$state` - Use for local UI state like loading spinners

#### Step 3: Create Backend Service (Service Worker)

Handle API requests and manage data in your service worker:

```typescript
// src/background/index.ts
import { createBackground } from '@fairfox/polly/background'
import type { AppMessages } from '../shared/messages'
import { currentUser } from '../shared/state'

const bus = createBackground<AppMessages>()

// API base URL (configurable)
const API_URL = 'https://api.example.com'

// Handle user fetch requests
bus.on('API_FETCH_USER', async (payload) => {
  try {
    const response = await fetch(`${API_URL}/users/${payload.userId}`)
    const data = await response.json()

    // Update shared state - automatically syncs to UI!
    currentUser.value = data

    return { success: true, data }
  } catch (error) {
    return { success: false, error: error.message }
  }
})

// Handle user updates
bus.on('API_UPDATE_USER', async (payload) => {
  try {
    const response = await fetch(`${API_URL}/users/${payload.userId}`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload.data)
    })
    const data = await response.json()

    currentUser.value = data

    return { success: true, data }
  } catch (error) {
    return { success: false, error: error.message }
  }
})

// Handle cache clearing
bus.on('CACHE_CLEAR', async () => {
  currentUser.value = null
  return { success: true }
})

console.log('Service worker ready!')
```

**Key insight:** You update state directly in the service worker (`currentUser.value = data`), and it automatically appears in your UI. No manual message sending required!

#### Step 4: Build Your UI

Create a reactive UI that updates automatically when state changes:

```typescript
// src/ui/App.tsx
import { render } from 'preact'
import { getMessageBus } from '@fairfox/polly/message-bus'
import { currentUser, settings } from '../shared/state'
import type { AppMessages } from '../shared/messages'

const bus = getMessageBus<AppMessages>('popup')

function App() {
  const handleFetchUser = async () => {
    const result = await bus.send({
      type: 'API_FETCH_USER',
      userId: '123'
    })

    if (!result.success) {
      alert(`Error: ${result.error}`)
    }
  }

  const handleUpdateUser = async () => {
    await bus.send({
      type: 'API_UPDATE_USER',
      userId: '123',
      data: {
        name: 'Jane Doe',
        email: 'jane@example.com',
        avatar: 'https://...'
      }
    })
  }

  return (
    <div className={`app theme-${settings.value.theme}`}>
      <h1>User Profile</h1>

      {/* Reactive - updates automatically! */}
      {currentUser.value ? (
        <div>
          <img src={currentUser.value.avatar} alt="Avatar" />
          <h2>{currentUser.value.name}</h2>
          <p>{currentUser.value.email}</p>
          <button onClick={handleUpdateUser}>Update Profile</button>
        </div>
      ) : (
        <button onClick={handleFetchUser}>Load User</button>
      )}

      <label>
        <input
          type="checkbox"
          checked={settings.value.notifications}
          onChange={(e) => {
            // Direct state update - syncs everywhere!
            settings.value = {
              ...settings.value,
              notifications: e.currentTarget.checked
            }
          }}
        />
        Enable Notifications
      </label>
    </div>
  )
}

render(<App />, document.getElementById('root')!)
```

**Key insight:** The UI automatically re-renders when `currentUser` or `settings` change, even if those changes come from the service worker or another tab!

#### Step 5: Build Your Application

```bash
# Create a polly.config.ts (optional)
export default {
  srcDir: 'src',
  distDir: 'dist',
  manifest: 'manifest.json'
}

# Build
polly build

# Build for production (minified)
polly build --prod

# Watch mode
polly dev
```

### The Polly Development Flow

Here's how to get the most out of Polly:

#### 1. Start with State Design

Think about what data needs to be:
- **Shared across contexts** → Use `$sharedState` or `$syncedState`
- **Persisted** → Use `$sharedState` or `$persistedState`
- **Local to a component** → Use `$state`

```typescript
// Good state design
export const userSession = $sharedState('session', null) // Persist login
export const wsConnection = $syncedState('ws', null)     // Don't persist socket
export const formData = $state({})                       // Local form state
```

#### 2. Define Messages as a Contract

Your message types are the contract between contexts. Define them explicitly:

```typescript
type CustomMessages =
  | { type: 'ACTION_NAME'; /* inputs */ }
  | { type: 'QUERY_NAME'; /* params */ }
```

Think of messages like API endpoints - they define the interface between your service worker and UI.

#### 3. Handle Business Logic in Background

The background/service worker is your "backend". Handle:
- API calls
- Data processing
- Chrome API interactions (tabs, storage, etc.)
- State updates

```typescript
bus.on('SOME_ACTION', async (payload) => {
  // 1. Do work
  const result = await doSomething(payload)

  // 2. Update state (auto-syncs to UI)
  myState.value = result

  // 3. Return response
  return { success: true, result }
})
```

#### 4. Keep UI Simple

Your UI just:
- Displays state
- Sends messages
- Updates local UI state

The UI should be "dumb" - all business logic lives in the background.

```typescript
function Component() {
  // Just render state and send messages!
  return (
    <div>
      <p>{myState.value}</p>
      <button onClick={() => bus.send({ type: 'DO_THING' })}>
        Click Me
      </button>
    </div>
  )
}
```

#### 5. Test with Real Browser APIs

Polly works with real Chrome/browser APIs, so you can test without mocks:

```typescript
// tests/app.test.ts
import { test, expect } from '@playwright/test'

test('user profile updates', async ({ page, extensionId }) => {
  await page.goto(`chrome-extension://${extensionId}/popup.html`)

  await page.click('[data-testid="fetch-user"]')

  // State automatically synced - just check the DOM!
  await expect(page.locator('[data-testid="user-name"]'))
    .toHaveText('Jane Doe')
})
```

### Full-Stack SPAs with Elysia (Bun)

Polly provides first-class support for building full-stack web applications with Elysia and Bun, treating your SPA as a distributed system.

**Why?** Modern SPAs are distributed systems facing classic distributed computing problems: network unreliability, eventual consistency, offline behavior, cache invalidation, and the CAP theorem. The Elysia integration makes these concerns explicit and verifiable.

#### Server: Add Polly Middleware

```typescript
// server/index.ts
import { Elysia, t } from 'elysia'
import { polly } from '@fairfox/polly/elysia'
import { $syncedState, $serverState } from '@fairfox/polly'

const app = new Elysia()
  .use(polly({
    // Define shared state
    state: {
      client: {
        todos: $syncedState('todos', []),
        user: $syncedState('user', null),
      },
      server: {
        db: $serverState('db', database),
      },
    },

    // Define client-side effects (what happens after server operations)
    effects: {
      'POST /todos': {
        client: ({ result, state }) => {
          // Update client state with new todo
          state.client.todos.value = [...state.client.todos.value, result]
        },
        broadcast: true,  // Notify all connected clients
      },
      'PATCH /todos/:id': {
        client: ({ result, state }) => {
          // Update specific todo in client state
          state.client.todos.value = state.client.todos.value.map(t =>
            t.id === result.id ? result : t
          )
        },
        broadcast: true,
      },
      'DELETE /todos/:id': {
        client: ({ params, state }) => {
          // Remove todo from client state
          state.client.todos.value = state.client.todos.value.filter(
            t => t.id !== Number(params.id)
          )
        },
        broadcast: true,
      },
    },

    // Define authorization rules
    authorization: {
      'POST /todos': ({ state }) => state.client.user.value !== null,
      'PATCH /todos/:id': ({ state }) => state.client.user.value !== null,
      'DELETE /todos/:id': ({ state }) => state.client.user.value !== null,
    },

    // Configure offline behavior
    offline: {
      'POST /todos': {
        queue: true,  // Queue when offline
        optimistic: (body) => ({
          id: -Date.now(),  // Temporary ID
          text: body.text,
          completed: false,
        }),
      },
    },

    // Enable TLA+ generation for verification
    tlaGeneration: true,
  }))

  // Write normal Elysia routes (no Polly annotations!)
  .post('/todos', async ({ body, pollyState }) => {
    const todo = await pollyState.server.db.value.todos.create(body)
    return todo
  }, {
    body: t.Object({ text: t.String() })
  })

  .listen(3000)
```

#### Client: Use Eden with Polly Wrapper

```typescript
// client/api.ts
import { createPollyClient } from '@fairfox/polly/client'
import { $syncedState } from '@fairfox/polly'
import type { app } from '../server'  // Import server type!

// Define client state
export const clientState = {
  todos: $syncedState('todos', []),
  user: $syncedState('user', null),
}

// Create type-safe API client (types inferred from server!)
export const api = createPollyClient<typeof app>('http://localhost:3000', {
  state: clientState,
  websocket: true,  // Enable real-time updates
})
```

```typescript
// client/components/TodoList.tsx
import { useSignal } from '@preact/signals'
import { api, clientState } from '../api'

export function TodoList() {
  const newTodo = useSignal('')

  async function handleAdd() {
    // Automatically handles:
    // - Optimistic update if offline
    // - Queue for retry
    // - Execute client effect on success
    // - Broadcast to other clients
    await api.todos.post({ text: newTodo.value })
    newTodo.value = ''
  }

  return (
    <div>
      {/* Connection status */}
      <div>Status: {api.$polly.state.isOnline.value ? '🟢 Online' : '🔴 Offline'}</div>

      {/* Queued requests indicator */}
      {api.$polly.state.queuedRequests.value.length > 0 && (
        <div>{api.$polly.state.queuedRequests.value.length} requests queued</div>
      )}

      {/* Todo list (automatically updates from state) */}
      <ul>
        {clientState.todos.value.map(todo => (
          <li key={todo.id}>
            <input
              type="checkbox"
              checked={todo.completed}
              onChange={() => api.todos[todo.id].patch({ completed: !todo.completed })}
            />
            <span>{todo.text}</span>
            <button onClick={() => api.todos[todo.id].delete()}>Delete</button>
          </li>
        ))}
      </ul>

      {/* Add new todo */}
      <input
        value={newTodo.value}
        onInput={(e) => newTodo.value = e.currentTarget.value}
        placeholder="What needs to be done?"
      />
      <button onClick={handleAdd}>Add</button>
    </div>
  )
}
```

#### Key Benefits

1. **Zero Type Duplication** - Eden infers client types from Elysia routes automatically
2. **Distributed Systems Semantics** - Explicit offline, authorization, and effects configuration
3. **Production-Ready** - Middleware is pass-through in production (minimal overhead)
4. **Real-Time Updates** - WebSocket broadcast keeps all clients in sync
5. **Formal Verification** - Generate TLA+ specs from middleware config to verify distributed properties

#### Production vs Development

**Development Mode:**
- Middleware adds metadata to responses for hot-reload and debugging
- Client effects serialized from server for live updates
- TLA+ generation enabled for verification

**Production Mode:**
- Middleware is minimal (authorization + broadcast only)
- Client effects are bundled at build time
- Zero serialization overhead

## Core Concepts

### State Primitives

Polly provides four state primitives, each for different use cases:

```typescript
// Syncs across contexts + persists to storage (most common)
const settings = $sharedState('settings', { theme: 'dark' })

// Syncs across contexts, no persistence (temporary shared state)
const activeTab = $syncedState('activeTab', null)

// Persists to storage, no sync (local persistent state)
const lastOpened = $persistedState('lastOpened', Date.now())

// Local only, no sync, no persistence (like regular Preact signals)
const loading = $state(false)
```

**When to use each:**

- **$sharedState**: User preferences, authentication state, application data
- **$syncedState**: WebSocket connections, temporary flags, live collaboration state
- **$persistedState**: Component-specific settings, form drafts
- **$state**: Loading indicators, modal visibility, form validation errors

### Message Patterns

#### Request/Response Pattern

```typescript
// Background: Handle requests
bus.on('GET_DATA', async (payload) => {
  const data = await fetchData(payload.id)
  return { success: true, data }
})

// UI: Send requests
const result = await bus.send({ type: 'GET_DATA', id: 123 })
if (result.success) {
  console.log(result.data)
}
```

#### Broadcast Pattern

```typescript
// Send to all contexts
bus.broadcast({ type: 'NOTIFICATION', message: 'Hello everyone!' })

// All contexts receive it
bus.on('NOTIFICATION', (payload) => {
  showToast(payload.message)
})
```

#### Fire and Forget

```typescript
// Don't await the response
bus.send({ type: 'LOG_EVENT', event: 'click' })
```

### Chrome Extension Specific

If you're building a Chrome extension:

```typescript
// Background script must use createBackground()
import { createBackground } from '@fairfox/polly/background'
const bus = createBackground<YourMessages>()

// Other contexts use getMessageBus()
import { getMessageBus } from '@fairfox/polly/message-bus'
const bus = getMessageBus<YourMessages>('popup')
```

**Important:** The background script creates a `MessageRouter` automatically. This routes messages between all contexts. Always use `createBackground()` in background scripts to ensure proper setup.

## CLI Tools

Polly includes CLI tools for development:

```bash
# Build your application
polly build [--prod]

# Type checking
polly typecheck

# Linting
polly lint [--fix]

# Formatting
polly format

# Run all checks
polly check

# Generate architecture diagrams
polly visualize [--export] [--serve]

# Formal verification (if configured)
polly verify [--setup]
```

## Architecture Visualization

Polly can analyze your codebase and generate architecture diagrams:

```bash
polly visualize
```

This creates a Structurizr DSL file documenting:
- Execution contexts (background, popup, etc.)
- Message flows between contexts
- External integrations (APIs, libraries)
- Chrome API usage

View the diagrams using Structurizr Lite:

```bash
docker run -it --rm -p 8080:8080 \
  -v $(pwd)/docs:/usr/local/structurizr \
  structurizr/lite
```

## Real-World Patterns

### API Client Pattern

```typescript
// src/background/api-client.ts
export class APIClient {
  constructor(private baseURL: string) {}

  async get<T>(path: string): Promise<T> {
    const response = await fetch(`${this.baseURL}${path}`)
    return response.json()
  }

  async post<T>(path: string, data: unknown): Promise<T> {
    const response = await fetch(`${this.baseURL}${path}`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(data)
    })
    return response.json()
  }
}

// src/background/index.ts
const api = new APIClient('https://api.example.com')

bus.on('API_REQUEST', async (payload) => {
  const data = await api.get(payload.endpoint)
  return { success: true, data }
})
```

### Offline Support Pattern

```typescript
// Cache API responses
const cache = $sharedState<Record<string, unknown>>('cache', {})

bus.on('API_FETCH', async (payload) => {
  // Check cache first
  if (cache.value[payload.url]) {
    return { success: true, data: cache.value[payload.url], cached: true }
  }

  try {
    const response = await fetch(payload.url)
    const data = await response.json()

    // Update cache
    cache.value = { ...cache.value, [payload.url]: data }

    return { success: true, data, cached: false }
  } catch (error) {
    // Fallback to cache if offline
    if (cache.value[payload.url]) {
      return { success: true, data: cache.value[payload.url], cached: true }
    }
    return { success: false, error: error.message }
  }
})
```

### Authentication Pattern

```typescript
// State
const authToken = $sharedState<string | null>('authToken', null)
const currentUser = $sharedState<User | null>('currentUser', null)

// Background
bus.on('AUTH_LOGIN', async (payload) => {
  const response = await fetch('https://api.example.com/auth/login', {
    method: 'POST',
    body: JSON.stringify(payload)
  })
  const { token, user } = await response.json()

  // Update state - syncs to all contexts
  authToken.value = token
  currentUser.value = user

  return { success: true }
})

bus.on('AUTH_LOGOUT', async () => {
  authToken.value = null
  currentUser.value = null
  return { success: true }
})

// UI
function LoginButton() {
  const handleLogin = async () => {
    await bus.send({
      type: 'AUTH_LOGIN',
      username: 'user',
      password: 'pass'
    })
  }

  return currentUser.value ? (
    <div>Welcome, {currentUser.value.name}</div>
  ) : (
    <button onClick={handleLogin}>Login</button>
  )
}
```

## Examples

Check out the [examples](https://github.com/AlexJeffcott/polly/tree/main/packages/examples) directory:

- **minimal** - Dead simple counter (best starting point)
- **full-featured** - Complete example with all features
- **todo-list** - Real-world CRUD application

## API Reference

### State

```typescript
import { $sharedState, $syncedState, $persistedState, $state } from '@fairfox/polly/state'

// Syncs + persists
const signal = $sharedState<T>(key: string, initialValue: T)

// Syncs, no persist
const signal = $syncedState<T>(key: string, initialValue: T)

// Persists, no sync
const signal = $persistedState<T>(key: string, initialValue: T)

// Local only
const signal = $state<T>(initialValue: T)

// All return Preact Signal<T>
signal.value        // Get value
signal.value = 42   // Set value
```

### Message Bus

```typescript
import { getMessageBus } from '@fairfox/polly/message-bus'
import { createBackground } from '@fairfox/polly/background'

// In background script
const bus = createBackground<YourMessages>()

// In other contexts
const bus = getMessageBus<YourMessages>('popup')

// Send message
const response = await bus.send({ type: 'MY_MESSAGE', data: 'foo' })

// Broadcast to all contexts
bus.broadcast({ type: 'NOTIFICATION', text: 'Hi!' })

// Handle messages
bus.on('MY_MESSAGE', async (payload) => {
  return { success: true }
})
```

### Types

```typescript
import type { ExtensionMessage } from '@fairfox/polly/types'

// Define custom messages
type CustomMessages =
  | { type: 'ACTION_ONE'; data: string }
  | { type: 'ACTION_TWO'; id: number }

// Combine with framework messages
type AllMessages = ExtensionMessage | CustomMessages
```

## How It Works

### State Synchronization

Polly uses **Lamport clocks** for distributed state consistency:

1. Each state update gets a logical timestamp
2. Updates are broadcast to all contexts
3. Contexts apply updates in causal order
4. Conflicts are resolved deterministically

This prevents race conditions when multiple contexts update state concurrently.

### Message Routing

The background context acts as a message hub:

1. Background starts a `MessageRouter`
2. Other contexts connect via `chrome.runtime.Port`
3. Messages are routed through the background
4. Responses are returned to the sender

This enables request/response patterns and broadcast messaging.

### Reactivity

Built on [Preact Signals](https://preactjs.com/guide/v10/signals/):

- Automatic UI updates when state changes
- Fine-grained reactivity (only affected components re-render)
- Works with Preact, React, Vue, Solid, etc.

## Requirements

- **Bun** 1.3+ (for building)
- **TypeScript** 5.0+ (recommended)
- **Chrome** 88+ (for Chrome extensions)

## License

MIT © 2024

---

**[Examples](https://github.com/AlexJeffcott/polly/tree/main/packages/examples)** · **[GitHub](https://github.com/AlexJeffcott/polly)** · **[Issues](https://github.com/AlexJeffcott/polly/issues)**
