# @fairfox/web-ext

**Build Chrome extensions with reactive state and zero boilerplate.**

Stop fighting Chrome's extension APIs. Write extensions like modern web apps.

```typescript
// Define state once
export const counter = $sharedState('counter', 0)

// Use everywhere - automatically syncs!
counter.value++  // Updates popup, options, background, everywhere
```

## Why?

Chrome extension development is painful:

- ❌ State scattered across contexts (popup, background, content scripts)
- ❌ Manual `chrome.storage` calls everywhere
- ❌ Complex message passing with `chrome.runtime.sendMessage`
- ❌ No reactivity - manually update UI when state changes
- ❌ Hard to test - mock 50+ Chrome APIs

This framework fixes all of that:

- ✅ **Reactive state** - UI updates automatically
- ✅ **Auto-syncing** - State syncs across all contexts instantly
- ✅ **Persistence** - State survives restarts (automatic)
- ✅ **Type-safe messaging** - Send messages between contexts easily
- ✅ **Built for testing** - DOM-based E2E tests with Playwright

## Quick Start

### Install

```bash
bun add @fairfox/web-ext
```

### Create Extension

**1. Define shared state** (automatically syncs everywhere):

```typescript
// src/shared/state.ts
import { $sharedState } from '@fairfox/web-ext/state'

export const counter = $sharedState('counter', 0)
export const settings = $sharedState('settings', { theme: 'dark' })
```

**2. Use in popup UI** (reactive - updates automatically):

```typescript
// src/popup/index.tsx
import { render } from 'preact'
import { counter } from '../shared/state'

function Popup() {
  return (
    <div>
      <p>Count: {counter.value}</p>
      <button onClick={() => counter.value++}>Increment</button>
    </div>
  )
}

render(<Popup />, document.getElementById('root')!)
```

**3. Setup background** (handles routing):

```typescript
// src/background/index.ts
import { createBackground } from '@fairfox/web-ext/background'

const bus = createBackground()
```

> **⚠️ Important:** Always use `createBackground()` in background scripts, not `getMessageBus('background')`.
> The framework protects against misconfiguration with singleton enforcement and automatic double-execution detection.
> See [Background Setup Guide](./docs/BACKGROUND_SETUP.md) for details.

**4. Build and load**:

```bash
bunx web-ext build
```

Load `dist/` folder in Chrome → **Done!** 🎉

## Features

### 🔄 Automatic State Sync

```typescript
// Change state anywhere
counter.value = 5

// Instantly appears EVERYWHERE:
// - Popup ✓
// - Options page ✓
// - Background ✓
// - All tabs ✓
```

### 💾 Automatic Persistence

```typescript
// State automatically saves to chrome.storage
const theme = $sharedState('theme', 'dark')

// Survives:
// - Extension reload ✓
// - Browser restart ✓
// - Chrome crash ✓
```

### ⚡️ Three Types of State

```typescript
// Syncs + persists (most common)
const settings = $sharedState('settings', { theme: 'dark' })

// Syncs, no persist (temporary shared state)
const activeTab = $syncedState('activeTab', null)

// Local only (like regular React state)
const loading = $state(false)
```

### 📡 Easy Message Passing

```typescript
// Background
bus.on('GET_DATA', async (payload) => {
  const data = await fetchData(payload.id)
  return { success: true, data }
})

// Popup
const result = await bus.send({ type: 'GET_DATA', id: 123 })
console.log(result.data)
```

### 🧪 Built for Testing

```typescript
// E2E tests with Playwright
test('counter increments', async ({ page }) => {
  await page.click('[data-testid="increment"]')
  const count = await page.locator('[data-testid="count"]').textContent()
  expect(count).toBe('1')
})
```

State automatically syncs during tests - no mocks needed!

## Examples

- [**Minimal**](./examples/minimal/) - Dead simple counter (30 lines)
- [**Full Featured**](./tests/framework-validation/test-extension/) - Shows all features
- More coming soon...

## Architecture

```
┌─────────────────────────────────────────┐
│  Your Extension                         │
├─────────────────────────────────────────┤
│  Popup    Options    Content Script    │
│    ↓         ↓            ↓             │
│  ┌─────────────────────────────────┐   │
│  │   Framework State Layer         │   │
│  │   (Auto-sync, Lamport clocks)   │   │
│  └─────────────────────────────────┘   │
│              ↓                          │
│  ┌─────────────────────────────────┐   │
│  │   Message Router (Background)   │   │
│  └─────────────────────────────────┘   │
│              ↓                          │
│  ┌─────────────────────────────────┐   │
│  │   Chrome Extension APIs         │   │
│  │   (storage, runtime, tabs)      │   │
│  └─────────────────────────────────┘   │
└─────────────────────────────────────────┘
```

## API Reference

### State Primitives

```typescript
// Syncs across contexts + persists to storage
$sharedState<T>(key: string, initialValue: T): Signal<T>

// Syncs across contexts (no persistence)
$syncedState<T>(key: string, initialValue: T): Signal<T>

// Persists to storage (no sync)
$persistedState<T>(key: string, initialValue: T): Signal<T>

// Local only (like Preact signal)
$state<T>(initialValue: T): Signal<T>
```

### Message Bus

```typescript
// Send message to background
await bus.send({ type: 'MY_MESSAGE', data: 'foo' })

// Broadcast to all contexts
bus.broadcast({ type: 'NOTIFICATION', text: 'Hello!' })

// Handle messages
bus.on('MY_MESSAGE', async (payload) => {
  return { success: true }
})
```

### Adapters

All Chrome APIs available via `bus.adapters`:

```typescript
// Storage
await bus.adapters.storage.set({ key: 'value' })
const data = await bus.adapters.storage.get('key')

// Tabs
const tabs = await bus.adapters.tabs.query({ active: true })

// Runtime
const id = bus.adapters.runtime.id
```

## How It Works

**State Synchronization:**
- Uses **Lamport clocks** for distributed consistency
- Broadcasts changes via `chrome.runtime` ports
- Conflict-free (CRDT-style convergence)

**Reactivity:**
- Built on [Preact Signals](https://preactjs.com/guide/v10/signals/)
- Automatic UI updates (no manual re-renders)
- Works with any framework (Preact, React, Vue, etc.)

**Message Routing:**
- Background acts as message hub
- Popup/Options/Content scripts connect via ports
- Type-safe request/response pattern

## Testing

Run the full test suite:

```bash
bun test                    # Unit tests
bun run test:framework      # E2E tests (Playwright)
```

All 16 E2E tests validate real Chrome extension behavior:
- ✅ State sync (popup ↔ options ↔ background)
- ✅ Persistence (survives reload)
- ✅ Reactivity (UI updates automatically)
- ✅ Message passing (request/response)
- ✅ Chrome APIs (storage, tabs, runtime)

## Requirements

- **Bun** 1.0+ (for building)
- **Chrome** 88+ (Manifest V3)
- **TypeScript** 5.0+ (recommended)

## Contributing

Contributions welcome! See [CONTRIBUTING.md](./CONTRIBUTING.md)

## Development

### TypeScript Configuration

This project uses separate TypeScript configs for source code and tests:

- **`tsconfig.json`** - Main config for source code (`src/`)
  - Strict mode enabled
  - Excludes `tests/` directory

- **`tsconfig.test.json`** - Config for test files (`tests/`)
  - Extends main config
  - Relaxes some strict rules for testing
  - Includes path mappings: `@/*` → `./src/*`

#### For Neovim/LSP Users

If your LSP shows errors about missing modules (like `@/shared/types/messages`), restart your LSP:
```vim
:LspRestart
```

Your LSP will automatically use the correct config based on which file you're editing.

## License

MIT © 2024

---

**[View Examples](./examples/)** · **[Read Docs](./docs/)** · **[Report Issue](https://github.com/fairfox/web-ext/issues)**
