# State Management

Universal reactive state primitives with automatic synchronization and persistence across execution contexts.

## Overview

Polly provides reactive state management that works seamlessly across different environments:
- **Chrome Extensions**: Multiple isolated contexts (background, popup, content scripts, etc.)
- **Web Applications & PWAs**: Multi-tab applications with cross-tab synchronization
- **Node.js/Testing**: In-memory state for verification and testing

The state primitives provide a unified API with automatic synchronization, persistence, and conflict resolution - the same code works everywhere with environment-specific optimizations.

## Quick Start

```typescript
import { $sharedState, $syncedState, $persistedState, $state } from '@fairfox/polly/state'

// Synced + Persisted (most common)
const settings = $sharedState('app-settings', {
  theme: 'dark',
  notifications: true
})

// Synced but not persisted
const activeTab = $syncedState('active-tab', null)

// Persisted but not synced
const uiState = $persistedState('popup:collapsed', false)

// Local only
const isLoading = $state(false)
```

## State Primitives

### `$sharedState(key, initialValue, options?)`

**Synced across all contexts AND persisted to storage.**

The most common state primitive. Use this for application settings, user preferences, and any data that should be shared and survive extension reloads.

**Features:**
- ✅ Synced across all contexts in real-time via environment-appropriate transport
- ✅ Persisted to storage (chrome.storage in extensions, IndexedDB in web apps)
- ✅ Lamport clock for conflict resolution
- ✅ Loads from storage on initialization
- ✅ Works in Chrome extensions AND web applications
- ⚠️ Not available in page scripts (isolated page context)

**Example:**
```typescript
const settings = $sharedState('settings', {
  theme: 'dark',
  autoSync: true,
  notifications: true
})

// Any context can read
console.log(settings.value.theme) // 'dark'

// Any context can write (syncs automatically)
settings.value = { ...settings.value, theme: 'light' }

// All contexts receive update instantly
// Storage is updated automatically
```

**Storage Keys:**
- `settings` → the state value
- `settings:clock` → Lamport clock for versioning

**⚠️ Automatic Persistence:**

`$sharedState` **automatically persists** to `chrome.storage.local` on every change. You do **NOT** need to call `storage.set()` manually.

```typescript
// ❌ Don't Do This - Redundant!
bookmarks.value = [...bookmarks.value, newItem];
await bus.adapters.storage.set({ bookmarks: bookmarks.value }); // REDUNDANT

// ✅ Do This Instead
bookmarks.value = [...bookmarks.value, newItem];
// That's it! Automatically persisted to storage.
```

The framework handles persistence automatically when you update the signal. Manual `storage.set()` calls are redundant and can cause unnecessary storage operations.

---

### `$syncedState(key, initialValue, options?)`

**Synced across all contexts but NOT persisted.**

Use for temporary shared state that doesn't need to survive extension reloads (active tab, selection state, ephemeral flags).

**Features:**
- ✅ Synced to all contexts in real-time
- ❌ Not persisted (resets on extension reload)
- ✅ Lamport clock for conflict resolution
- ⚠️ Not available in page scripts

**Example:**
```typescript
const currentTab = $syncedState('current-tab', null)

// Background tracks active tab
chrome.tabs.onActivated.addListener(({ tabId }) => {
  currentTab.value = tabId
})

// Popup sees the update instantly
console.log(currentTab.value) // 123
```

---

### `$persistedState(key, initialValue, options?)`

**Persisted to storage but NOT synced across contexts.**

Use for context-specific preferences that should persist but don't need to be shared (UI state like "is sidebar collapsed", "last opened panel").

**Features:**
- ❌ Not synced (each context has its own copy)
- ✅ Persisted to `chrome.storage.local`
- ✅ Survives extension reloads
- ⚠️ Not available in page scripts

**Example:**
```typescript
// Popup has its own state
const popupState = $persistedState('popup:last-panel', 'home')

// DevTools has its own state
const devtoolsState = $persistedState('devtools:expanded', true)

// They don't affect each other
popupState.value = 'settings' // DevTools state unchanged
```

**Best Practice:** Use prefixes like `popup:`, `devtools:`, `options:` to avoid key collisions.

---

### `$state(initialValue)`

**Local reactive state (not synced, not persisted).**

A thin wrapper around Preact's `signal()`. Use for component-local state like loading flags, form inputs, temporary UI state.

**Features:**
- ❌ Not synced
- ❌ Not persisted
- ✅ Available in ALL contexts (including page scripts)
- ✅ Fast (no storage or messaging overhead)

**Example:**
```typescript
const isLoading = $state(false)
const error = $state<string | null>(null)
const formData = $state({ name: '', email: '' })

async function submit() {
  isLoading.value = true
  try {
    await api.post(formData.value)
  } catch (e) {
    error.value = e.message
  } finally {
    isLoading.value = false
  }
}
```

---

## Universal Architecture

Polly automatically detects your environment and uses the appropriate adapters for storage and synchronization:

### Environment Detection

| Environment | Storage | Sync Transport | Use Case |
|------------|---------|----------------|----------|
| **Chrome Extension** | `chrome.storage.local` | `chrome.runtime` messaging | Multi-context extensions |
| **Web App / PWA** | IndexedDB | BroadcastChannel | Multi-tab web applications |
| **Single-Tab Web App** | IndexedDB | None (NoOp) | Single-tab applications |
| **Node.js / Testing** | In-memory | None (NoOp) | Verification & unit tests |

**How it works:**

```typescript
// Same code, different environments:
const settings = $sharedState('settings', { theme: 'dark' })

// In Chrome extension:
//   - Uses chrome.storage.local for persistence
//   - Uses chrome.runtime.sendMessage for sync

// In web app:
//   - Uses IndexedDB for persistence
//   - Uses BroadcastChannel for cross-tab sync

// In Node.js tests:
//   - Uses in-memory Map for storage
//   - No sync (single process)
```

### Storage Adapters

The framework automatically selects the right storage backend:

1. **ChromeStorageAdapter**: Uses `chrome.storage.local` (extensions)
2. **IndexedDBAdapter**: Uses IndexedDB (web apps/PWAs)
3. **MemoryStorageAdapter**: Uses Map (testing/verification)

### Sync Adapters

Cross-context synchronization uses environment-appropriate transport:

1. **ChromeRuntimeSyncAdapter**: Uses `chrome.runtime.sendMessage` (extensions)
2. **BroadcastChannelSyncAdapter**: Uses BroadcastChannel API (web apps)
3. **NoOpSyncAdapter**: No sync (single-context scenarios)

**Why BroadcastChannel for web apps?**

BroadcastChannel provides peer-to-peer messaging between tabs with minimal overhead. See [Architecture Decision](../src/shared/lib/sync-adapter.ts) for comparison with SharedWorker and rationale.

### Custom Adapters

You can provide custom adapters for specialized scenarios:

```typescript
import { $sharedState } from '@fairfox/polly/state'
import { IndexedDBAdapter, BroadcastChannelSyncAdapter } from '@fairfox/polly/adapters'

const settings = $sharedState('settings', defaultSettings, {
  storage: new IndexedDBAdapter('my-db-name'),
  sync: new BroadcastChannelSyncAdapter('my-channel'),
})
```

---

## Context Availability

| Primitive | Background | Popup | Options | DevTools | Content | Web App | Page |
|-----------|-----------|-------|---------|----------|---------|---------|------|
| `$sharedState` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| `$syncedState` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| `$persistedState` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| `$state` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

**Why not page scripts?**

Page scripts run in the webpage's JavaScript context (when injected via `<script>` tag). They don't have access to extension APIs or reliable storage. Use content scripts for stateful operations instead.

---

## How It Works

### Lamport Clock

State uses a [Lamport clock](https://en.wikipedia.org/wiki/Lamport_timestamp) for conflict resolution. Each update increments a monotonic counter:

```typescript
// Context A
settings.value = { theme: 'dark' }  // clock: 5 → 6

// Context B (simultaneously)
settings.value = { theme: 'light' } // clock: 5 → 6

// Both broadcast clock 6
// Storage last-write-wins
// Next update syncs everyone
```

**Key Properties:**
- Monotonically increasing (never decreases)
- Older updates are rejected (`incoming.clock <= current.clock`)
- No timestamp dependency (immune to clock skew)
- Eventually consistent

### Storage + Sync Adapters

State uses **two independent channels** for synchronization via the adapter pattern:

1. **Storage Adapter** - Persistent source of truth (chrome.storage, IndexedDB, or in-memory)
2. **Sync Adapter** - Real-time synchronization (chrome.runtime, BroadcastChannel, or NoOp)

```
Context A changes state
    ↓
    ├─→ Write to storage adapter (durability)
    └─→ Broadcast via sync adapter (real-time)
        ↓
Context B receives message
    └─→ Updates local signal instantly
```

This hybrid approach provides:
- **Real-time sync** via environment-appropriate messaging (no polling)
- **Durability** via environment-appropriate storage (survives crashes)
- **Consistency** via Lamport clock (conflict resolution)
- **Universality** via adapters (same code, different environments)

### Deep Equality

To prevent redundant updates, state performs deep equality checks:

```typescript
// Current value
settings.value = { theme: 'dark', notifications: true }

// Incoming sync message with same value
if (deepEqual(current, incoming)) {
  // Skip update (but update clock to stay in sync)
  entry.clock = incoming.clock
  return
}
```

This prevents:
- Unnecessary re-renders
- Redundant storage writes
- Message loops

---

## Options

### Validator

Validate state values at runtime (useful for data from storage or other contexts):

```typescript
type Settings = {
  theme: 'light' | 'dark'
  notifications: boolean
}

const settings = $sharedState('settings', defaultSettings, {
  validator: (value): value is Settings => {
    return (
      typeof value === 'object' &&
      value !== null &&
      ('theme' in value) &&
      (value.theme === 'light' || value.theme === 'dark') &&
      ('notifications' in value) &&
      typeof value.notifications === 'boolean'
    )
  }
})
```

**When validation fails:**
- On load from storage: Uses `initialValue` instead
- On sync message: Rejects update and logs warning

```
[web-ext] State "settings": Stored value failed validation, using initial value
[web-ext] State "settings": Received invalid value from sync (clock: 42)
```

### Debounce

Debounce storage writes for high-frequency updates:

```typescript
const cursorPosition = $sharedState('cursor', { x: 0, y: 0 }, {
  debounceMs: 500 // Wait 500ms after last change before writing
})

// User moves mouse rapidly
cursorPosition.value = { x: 10, y: 20 }
cursorPosition.value = { x: 11, y: 21 }
cursorPosition.value = { x: 12, y: 22 }
// Only writes once, 500ms after last update
```

**Benefits:**
- Reduces storage API calls
- Improves performance
- Messages still send immediately (sync not debounced)

### Verify (TLA+ Verification)

Enable automatic TLA+ state transition extraction for formal verification:

```typescript
const authState = $sharedState('auth', {
  isAuthenticated: false,
  userProfile: null,
}, { verify: true })
```

When `verify: true` is set, the TLA+ generator will:

1. **Discover the state signal** - Finds all `$sharedState`, `$syncedState`, and `$persistedState` declarations with verification enabled
2. **Find state-modifying functions** - Automatically detects exported functions that modify the state
3. **Extract verification conditions** - Pulls `requires()` and `ensures()` annotations from those functions
4. **Generate TLA+ transitions** - Creates proper state transitions instead of `UNCHANGED contextStates`

**Example with verification annotations:**

```typescript
import { requires, ensures } from '@fairfox/polly/verify'

export const authState = $sharedState('auth', {
  isAuthenticated: false,
  userProfile: null,
}, { verify: true })

export function handleAuthSuccess(userProfile: UserProfile): void {
  requires(!authState.value.isAuthenticated, 'Must not already be authenticated')

  authState.value = {
    ...authState.value,
    isAuthenticated: true,
    userProfile,
  }

  ensures(authState.value.isAuthenticated, 'Must be authenticated after success')
}

export function handleLogout(): void {
  requires(authState.value.isAuthenticated, 'Must be authenticated to logout')

  authState.value = {
    ...authState.value,
    isAuthenticated: false,
    userProfile: null,
  }

  ensures(!authState.value.isAuthenticated, 'Must not be authenticated after logout')
}
```

**Generated TLA+ (example):**

```tla
HandleAuthSuccess(ctx) ==
  /\ contextStates[ctx].isAuthenticated = FALSE  \* requires
  /\ contextStates' = [contextStates EXCEPT
       ![ctx].isAuthenticated = TRUE,
       ![ctx].userProfile = payload]
  /\ contextStates'[ctx].isAuthenticated = TRUE  \* ensures

HandleLogout(ctx) ==
  /\ contextStates[ctx].isAuthenticated = TRUE   \* requires
  /\ contextStates' = [contextStates EXCEPT
       ![ctx].isAuthenticated = FALSE,
       ![ctx].userProfile = NULL]
  /\ contextStates'[ctx].isAuthenticated = FALSE \* ensures
```

**Function name to message type conversion:**
- `handleAuthSuccess` → `AuthSuccess`
- `handleLogout` → `Logout`
- `setUserProfile` → `SetUserProfile`
- `updateSettings` → `UpdateSettings`

This pattern is ideal for:
- **Multi-tab PWAs** with cross-tab state synchronization
- **WebSocket applications** where state is modified by reactive effects
- **Event-driven architectures** where handlers aren't registered via `messageBus.on()`

---

## Waiting for Hydration

`$sharedState` **automatically loads** from `chrome.storage.local` on initialization. However, this load is asynchronous. If you need to wait for the storage load to complete before using the state, you can await the `.loaded` promise:

```typescript
const settings = $sharedState('settings', defaultSettings);

// Wait for storage load to complete
await settings.loaded;

// Now settings.value is guaranteed to have the loaded value from storage
console.log(settings.value.theme); // Value from storage, not just initialValue
```

**⚠️ Automatic Hydration:**

You do **NOT** need to manually load state from storage. The framework handles this automatically.

```typescript
// ❌ Don't Do This - Redundant!
(async () => {
  const stored = await bus.adapters.storage.get(["settings"]);
  if (isSettings(stored.settings)) {
    settings.value = stored.settings; // REDUNDANT
  }
})();

// ✅ Do This Instead
const settings = $sharedState("settings", defaultSettings);
// Automatically loads from storage in the background

// Or if you need to wait:
await settings.loaded;
console.log(settings.value); // Loaded from storage
```

**When to await `.loaded`:**
- Before reading state that MUST be from storage (not initialValue)
- In background script initialization
- When state is critical for immediate operations

**When NOT to await `.loaded`:**
- In UI components (they'll re-render when state loads)
- When initialValue is a reasonable default
- For non-critical state that can update asynchronously

---

## Best Practices

### 1. Use Descriptive Keys

```typescript
// ✅ Good - clear and descriptive
$sharedState('user-settings', {...})
$sharedState('api-cache', {...})
$persistedState('popup:last-opened-tab', 'home')

// ❌ Bad - unclear or collision-prone
$sharedState('data', {...})
$sharedState('state', {...})
$persistedState('tab', 'home') // Collides across contexts
```

### 2. Namespace Context-Specific State

```typescript
// ✅ Good - prefixed with context
$persistedState('popup:sidebar-collapsed', false)
$persistedState('devtools:filter-active', true)
$persistedState('options:theme-preview', 'dark')

// ❌ Bad - no prefix, keys collide
$persistedState('collapsed', false)
$persistedState('active', true)
$persistedState('preview', 'dark')
```

### 3. Choose the Right Primitive

| Use Case | Primitive |
|----------|-----------|
| App settings | `$sharedState` |
| User preferences | `$sharedState` |
| Authentication state | `$sharedState` |
| Active tab tracking | `$syncedState` |
| Selection state | `$syncedState` |
| Temporary flags | `$syncedState` |
| UI preferences (per context) | `$persistedState` |
| Sidebar collapsed state | `$persistedState` |
| Loading flags | `$state` |
| Form inputs | `$state` |
| Hover state | `$state` |

### 4. Define State in Shared Module

```typescript
// ✅ Good - single source of truth
// src/shared/state/app-state.ts
export const settings = $sharedState('settings', defaultSettings)
export const user = $sharedState('user', null)

// Import anywhere
import { settings } from '@/shared/state/app-state'
```

### 5. Use TypeScript

```typescript
// ✅ Good - fully typed
type Settings = {
  theme: 'light' | 'dark'
  notifications: boolean
}

const settings = $sharedState<Settings>('settings', {
  theme: 'dark',
  notifications: true
})

settings.value.theme = 'auto' // ❌ Type error

// ✅ Good - nullable types
const user = $sharedState<User | null>('user', null)
```

### 6. Don't Store Large Data

State is optimized for small, frequently-updated data (settings, preferences, flags). For large data:

```typescript
// ❌ Bad - large data in state
const cache = $sharedState('cache', {
  // 10MB of cached API responses
})

// ✅ Good - use storage API directly
async function getCache() {
  return await chrome.storage.local.get('cache')
}

async function setCache(data) {
  await chrome.storage.local.set({ cache: data })
}
```

### 7. Avoid Deep Mutations

Signals require reassignment to trigger updates:

```typescript
const settings = $sharedState('settings', { theme: 'dark' })

// ❌ Bad - mutates without triggering update
settings.value.theme = 'light'

// ✅ Good - reassign to trigger update
settings.value = { ...settings.value, theme: 'light' }
```

---

## Computed State

Use Preact's `computed()` for derived state:

```typescript
import { computed } from '@preact/signals'

const settings = $sharedState('settings', {
  theme: 'dark',
  apiEndpoint: 'https://api.example.com'
})

// Computed values auto-update
const isDarkMode = computed(() => settings.value.theme === 'dark')
const apiUrl = computed(() => new URL(settings.value.apiEndpoint))

// Use in components
<div className={isDarkMode.value ? 'dark' : 'light'}>
  API: {apiUrl.value.hostname}
</div>
```

**Note:** Don't sync computed values - they derive from synced state automatically.

---

## Patterns

### Settings with Validation

```typescript
import { z } from 'zod'

const SettingsSchema = z.object({
  theme: z.enum(['light', 'dark', 'auto']),
  notifications: z.boolean(),
  apiEndpoint: z.string().url()
})

type Settings = z.infer<typeof SettingsSchema>

const settings = $sharedState<Settings>('settings', defaultSettings, {
  validator: (value): value is Settings => {
    return SettingsSchema.safeParse(value).success
  }
})
```

### Global Loading State

```typescript
// Synced loading state visible in all contexts
const isLoading = $syncedState('global-loading', false)

// Background starts long operation
async function syncData() {
  isLoading.value = true
  try {
    await longRunningOperation()
  } finally {
    isLoading.value = false
  }
}

// Popup shows loading indicator
<div>{isLoading.value && <Spinner />}</div>
```

### Context-Aware State

```typescript
// Each context has independent UI state
const getUiState = () => {
  const context = getCurrentContext()
  return $persistedState(`${context}:ui-state`, {
    sidebarOpen: false,
    activePanel: 'main'
  })
}

const uiState = getUiState()
```

### Migration from Old Values

```typescript
const settings = $sharedState('settings-v2', defaultSettings)

// Migrate from old key on first load
chrome.storage.local.get('settings-v1').then(result => {
  if (result['settings-v1']) {
    const migrated = migrateV1ToV2(result['settings-v1'])
    settings.value = migrated
    chrome.storage.local.remove('settings-v1')
  }
})
```

---

## Architecture

### State Entry

Internally, each state is stored as a `StateEntry`:

```typescript
type StateEntry<T> = {
  signal: Signal<T>          // Preact signal
  clock: number               // Lamport clock
  loaded: Promise<void>       // Storage load complete
  updating: boolean           // Lock flag (prevents loops)
}
```

### Registry

States are registered in a per-context Map:

```typescript
const stateRegistry = new Map<string, StateEntry<unknown>>()
```

Calling `$sharedState('settings', ...)` multiple times returns the **same signal instance** within a context.

### Load Sequence

```
1. createState() called
2. Create signal with initialValue
3. Load from storage (async)
   ├─ Read value + clock
   ├─ Validate if validator provided
   └─ Update signal
4. Wait for load to complete
5. Start watching for changes
   └─ effect() triggers on signal updates
       ├─ Increment clock
       ├─ Write to storage (debounced if configured)
       └─ Broadcast to other contexts
6. Listen for incoming sync messages
   └─ Validate clock (reject old)
   └─ Validate value (if validator)
   └─ Check deep equality (skip redundant)
   └─ Apply update
```

### Message Flow

```
Context A: User changes state
    ↓
effect() fires
    ↓
clock: 5 → 6
    ↓
    ├─→ chrome.storage.set({ key: value, key:clock: 6 })
    └─→ bus.broadcast({ type: 'STATE_SYNC', key, value, clock: 6 })
            ↓
        Context B receives message
            ↓
        Check: payload.clock > entry.clock? (6 > 5) ✅
            ↓
        Validate payload.value ✅
            ↓
        Deep equal check ❌ (different)
            ↓
        entry.updating = true (lock)
        entry.signal.value = payload.value
        entry.clock = 6
        entry.updating = false
            ↓
        Context B updated!
```

---

## Troubleshooting

### State not syncing

**Symptoms:** Changes in one context don't appear in another

**Causes:**
1. Using `$persistedState` instead of `$sharedState`
2. Page script trying to use stateful primitives
3. MessageBus not initialized

**Solutions:**
```typescript
// ✅ Use $sharedState for syncing
const settings = $sharedState('settings', {})

// ✅ Check context
console.log('Context:', getCurrentContext())

// ✅ Verify MessageBus
const bus = getMessageBus(context)
console.log('Bus:', bus.context)
```

### State not persisting

**Symptoms:** State resets on extension reload

**Causes:**
1. Using `$syncedState` instead of `$sharedState`
2. Using `$state` (local only)

**Solutions:**
```typescript
// ✅ Use $sharedState or $persistedState
const settings = $sharedState('settings', {})
```

### Validation errors

**Symptoms:** Console warnings about validation failures

```
[web-ext] State "settings": Stored value failed validation
```

**Causes:**
1. Storage contains old/invalid data
2. Validator is too strict
3. Type changed between versions

**Solutions:**
```typescript
// ✅ Make validator lenient for backwards compatibility
validator: (value): value is Settings => {
  if (!value || typeof value !== 'object') return false
  // Check required fields only
  return 'theme' in value
}

// ✅ Or migrate data
chrome.storage.local.get('settings').then(result => {
  const old = result.settings
  if (!isValidV2(old)) {
    const migrated = migrateV1ToV2(old)
    chrome.storage.local.set({ settings: migrated })
  }
})
```

### Clock conflicts

**Symptoms:** State oscillates between values

**Causes:**
1. Multiple contexts updating simultaneously
2. Clock not syncing properly

**Solutions:**
- This is expected behavior for concurrent updates
- Storage will resolve conflicts via last-write-wins
- Next update will sync everyone
- If critical, use a lock mechanism in your application logic

---

## API Reference

### `$sharedState<T>(key: string, initialValue: T, options?: StateOptions<T>): Signal<T>`

Create synced + persisted state.

**Parameters:**
- `key` - Unique identifier (e.g., `"app-settings"`)
- `initialValue` - Default value if nothing in storage
- `options.storage` - Optional custom StorageAdapter
- `options.sync` - Optional custom SyncAdapter
- `options.validator` - Optional runtime type guard
- `options.verify` - Optional boolean; when `true`, creates a `.verify` plain-object mirror for TLA+ verification
- `options.debounceMs` - Optional debounce for storage writes
- `options.bus` - Optional custom MessageBus (deprecated, use adapters)

**Returns:** Reactive Preact signal

---

### `$syncedState<T>(key: string, initialValue: T, options?: StateOptions<T>): Signal<T>`

Create synced but NOT persisted state.

**Parameters:** Same as `$sharedState`

**Returns:** Reactive Preact signal

---

### `$persistedState<T>(key: string, initialValue: T, options?: StateOptions<T>): Signal<T>`

Create persisted but NOT synced state.

**Parameters:** Same as `$sharedState`

**Returns:** Reactive Preact signal

---

### `$state<T>(initialValue: T): Signal<T>`

Create local reactive state.

**Parameters:**
- `initialValue` - Default value

**Returns:** Reactive Preact signal

---

### `getStateByKey<T>(key: string): Signal<T> | undefined`

Retrieve existing state by key (without creating new one).

**Parameters:**
- `key` - State key

**Returns:** Signal if exists, undefined otherwise

---

### `clearStateRegistry(): void`

Clear all registered states (useful for testing).

---

## Examples

See `src/shared/state/app-state.ts` for production usage.
