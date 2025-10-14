# Test Extension

This is a test extension for validating the web-ext framework with comprehensive tests across **all extension contexts**.

## Structure

```
test-extension/
├── src/
│   ├── shared/
│   │   └── types/
│   │       └── test-messages.ts         # Custom message types
│   ├── background/
│   │   └── test-handlers.ts             # Background message handlers
│   ├── content/
│   │   └── test-content.ts              # Content script implementation
│   ├── popup/
│   │   └── test-popup.ts                # Popup UI and handlers
│   ├── options/
│   │   └── test-options.ts              # Options page implementation
│   ├── devtools/
│   │   └── test-devtools-panel.ts       # DevTools panel implementation
│   └── sidepanel/
│       └── test-sidepanel.ts            # Side panel implementation
├── tsconfig.json                         # TypeScript configuration
└── README.md
```

## TypeScript Setup

### Option 1: Using Path Aliases (Recommended)

Create a `tsconfig.json` with path mappings:

```json
{
  "compilerOptions": {
    "target": "ES2020",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "strict": true,
    "baseUrl": ".",
    "paths": {
      "@/*": ["./node_modules/@fairfox/web-ext/*"]
    },
    "types": ["chrome"]
  }
}
```

This allows clean imports:
```typescript
import { createContext } from '@/shared/lib/context-helpers'
import { getMessageBus } from '@/shared/lib/message-bus'
```

### Option 2: Relative Imports

Without path aliases, use relative imports:

```typescript
import { createContext } from '../../node_modules/@fairfox/web-ext/shared/lib/context-helpers'
import { getMessageBus } from '../../node_modules/@fairfox/web-ext/shared/lib/message-bus'
```

### Option 3: Package Imports (When Published)

Once the framework is published to npm:

```typescript
import { createContext, getMessageBus } from '@fairfox/web-ext'
```

**For this example:** The `tsconfig.json` is configured to point to the framework source at `../../../src/*` for development.

## Extension Contexts Overview

Web extensions run in multiple isolated contexts, each with different capabilities:

| Context | Purpose | Capabilities | Lifetime |
|---------|---------|--------------|----------|
| **Background** | Service worker for extension logic | Full Chrome APIs, no DOM access | Event-driven |
| **Content Script** | Runs in web pages | DOM access, limited Chrome APIs | Per-page load |
| **Popup** | UI when clicking extension icon | Full Chrome APIs, has DOM | Short-lived |
| **Options** | Full-page settings interface | Full Chrome APIs, has DOM | User-opened |
| **DevTools** | Panel in Chrome DevTools | Can inspect page, full Chrome APIs | While DevTools open |
| **Side Panel** | Persistent companion panel | Full Chrome APIs, has DOM | Persistent |

## How to Use the Framework in Each Context

### 1. Define Your Custom Messages

```typescript
// src/shared/types/custom-messages.ts
import type { ExtensionMessage } from '@/shared/types/messages'

// Define your custom messages
export type CustomMessages =
  | { type: "MY_FEATURE"; data: string }
  | { type: "ANOTHER_FEATURE"; count: number }
  | { type: "GET_USER_SETTINGS" }

// Combine with framework messages
export type AllMessages = ExtensionMessage | CustomMessages
```

### 2. Background Script

The background script is the central hub that typically handles most message routing.

```typescript
// src/background/index.ts
import { getMessageBus } from '@/shared/lib/message-bus'

const bus = getMessageBus('background')

// Register handlers
bus.on('MY_FEATURE', async (payload) => {
  // Access Chrome APIs
  const tabs = await bus.adapters.tabs.query({})

  // Store data
  await bus.adapters.storage.set({ myData: payload.data })

  return { success: true, tabCount: tabs.length }
})

console.log('[Background] Initialized')
```

### 3. Content Script

Content scripts run in web pages and can access the DOM. They communicate with the background script via the message bus.

```typescript
// src/content/index.ts
import { getMessageBus } from '@/shared/lib/message-bus'

const bus = getMessageBus('content')

// Register handlers that can access the DOM
bus.on('MY_FEATURE', async (payload) => {
  return {
    success: true,
    context: 'content',
    pageInfo: {
      url: window.location.href,
      title: document.title,
    }
  }
})

// Send messages to background
async function analyzePageContent() {
  const result = await bus.send({
    type: 'ANOTHER_FEATURE',
    count: document.querySelectorAll('a').length
  })

  console.log('[Content] Result:', result)
}

// Listen for DOM events
document.addEventListener('click', (e) => {
  bus.send({
    type: 'MY_FEATURE',
    data: (e.target as HTMLElement).tagName
  }).catch(console.error)
})
```

### 4. Popup

Popups are short-lived UIs that appear when users click the extension icon.

```typescript
// src/popup/index.ts
import { getMessageBus } from '@/shared/lib/message-bus'
import { settings } from '@/shared/state/app-state'

const bus = getMessageBus('popup')

// Register handlers
bus.on('MY_FEATURE', async (payload) => {
  // Update UI based on results
  updateUIWithResults(payload)
  return { success: true, context: 'popup' }
})

// Setup UI interactions
document.getElementById('my-button')?.addEventListener('click', async () => {
  // Send message to background
  const result = await bus.send({
    type: 'MY_FEATURE',
    data: 'user-clicked-button'
  })

  // Update UI
  displayResults(result)
})

// Access reactive state
settings.value // Automatically synced across contexts
```

### 5. Options Page

Options pages provide full-page settings interfaces.

```typescript
// src/options/index.ts
import { getMessageBus } from '@/shared/lib/message-bus'
import { settings } from '@/shared/state/app-state'
import { effect } from '@preact/signals-core'

const bus = getMessageBus('options')

// Save settings
async function saveSettings() {
  const newSettings = {
    theme: document.querySelector('#theme').value,
    enabled: document.querySelector('#enabled').checked
  }

  // Store in Chrome storage
  await bus.adapters.storage.set(newSettings)

  // Update signals (automatically syncs to other contexts)
  settings.value = { ...settings.value, ...newSettings }

  // Notify background
  await bus.send({ type: 'SETTINGS_UPDATED' })
}

// React to settings changes from other contexts
effect(() => {
  console.log('[Options] Settings changed:', settings.value)
  updateUIWithSettings(settings.value)
})
```

### 6. DevTools Panel

DevTools panels can inspect and interact with web pages.

```typescript
// src/devtools/panel.ts
import { getMessageBus } from '@/shared/lib/message-bus'

const bus = getMessageBus('devtools')

// Get inspected tab ID
const tabId = chrome.devtools.inspectedWindow.tabId

// Execute code in inspected page
function inspectPage() {
  chrome.devtools.inspectedWindow.eval(`
    ({
      url: window.location.href,
      title: document.title,
      elements: document.querySelectorAll('*').length
    })
  `, (result, error) => {
    if (!error) {
      console.log('[DevTools] Page data:', result)
    }
  })
}

// Communicate with background
async function getExtensionData() {
  const result = await bus.send({ type: 'GET_USER_SETTINGS' })
  updateDevToolsUI(result)
}
```

### 7. Side Panel

Side panels provide persistent companion interfaces (Chrome 114+).

```typescript
// src/sidepanel/index.ts
import { getMessageBus } from '@/shared/lib/message-bus'
import { settings } from '@/shared/state/app-state'

const bus = getMessageBus('sidepanel')

// Listen for tab changes
chrome.tabs.onActivated.addListener(async (activeInfo) => {
  const result = await bus.send({ type: 'MY_FEATURE', data: 'tab-changed' })
  updateSidePanelUI(result)
})

// Side panels remain open, so they can maintain state
let sessionData = {
  visits: 0,
  interactions: []
}

// React to settings changes
effect(() => {
  console.log('[Side Panel] Settings updated:', settings.value)
  applyTheme(settings.value.theme)
})
```

## Cross-Context Communication Patterns

### Pattern 1: Request-Response

Any context can send a message and wait for a response:

```typescript
// From any context
const result = await bus.send({ type: 'MY_FEATURE', data: 'test' })
console.log('Response:', result)
```

### Pattern 2: Broadcast Events

Background can broadcast events to all contexts:

```typescript
// Background
bus.broadcast({ type: 'SETTINGS_CHANGED', newSettings })

// All contexts with handlers receive it
bus.on('SETTINGS_CHANGED', (payload) => {
  console.log('Settings changed:', payload.newSettings)
})
```

### Pattern 3: Shared State (Signals)

Use signals for reactive, cross-context state:

```typescript
import { settings } from '@/shared/state/app-state'

// Any context can read
console.log(settings.value)

// Any context can update (automatically syncs)
settings.value = { ...settings.value, theme: 'dark' }

// Any context can react to changes
effect(() => {
  console.log('Settings changed:', settings.value)
})
```

### Pattern 4: Content Script ↔ Background

Content scripts commonly need to communicate with background:

```typescript
// Content script requests data from background
const tabs = await bus.send({ type: 'GET_ALL_TABS' })

// Background responds
bus.on('GET_ALL_TABS', async () => {
  const tabs = await bus.adapters.tabs.query({})
  return { tabs }
})
```

## Context-Specific Capabilities

### What Each Context Can Do

**Background Script:**
- ✅ Full Chrome API access
- ✅ Long-lived (service worker)
- ✅ Central message hub
- ❌ No DOM access
- ❌ No direct page interaction

**Content Script:**
- ✅ Full DOM access
- ✅ Can inject UI into pages
- ✅ Runs in page context
- ❌ Limited Chrome APIs
- ❌ Isolated from page JavaScript

**Popup:**
- ✅ Full Chrome API access
- ✅ Has DOM for UI
- ✅ Quick user interactions
- ⚠️ Short-lived (closes easily)
- ❌ Limited space

**Options Page:**
- ✅ Full Chrome API access
- ✅ Full-page UI
- ✅ Perfect for complex settings
- ✅ Can use any web framework
- ⚠️ User must open manually

**DevTools Panel:**
- ✅ Can inspect active tab
- ✅ Access to page console
- ✅ Execute code in page
- ⚠️ Only available when DevTools open

**Side Panel:**
- ✅ Persistent UI
- ✅ Full Chrome API access
- ✅ Stays open across tabs
- ✅ Modern, spacious interface
- ⚠️ Chrome 114+ only

## Testing Pattern

This example extension demonstrates the testing pattern:

1. Each context implements handlers for test messages
2. Handlers exercise framework features (storage, tabs, logging, etc.)
3. Results are stored in `window.__[CONTEXT]_TEST_RESULTS__`
4. Playwright validates the results from each context

This proves the framework works end-to-end with real Chrome APIs across all extension contexts.

## Example: Complete Feature Flow

Here's how a complete feature might work across contexts:

```typescript
// 1. User clicks button in POPUP
document.getElementById('analyze-btn').addEventListener('click', async () => {
  // 2. Popup asks BACKGROUND for current tab
  const { currentTab } = await bus.send({ type: 'GET_CURRENT_TAB' })

  // 3. Popup sends message to CONTENT SCRIPT in that tab
  const pageData = await bus.send({
    type: 'ANALYZE_PAGE',
    tabId: currentTab.id
  })

  // 4. BACKGROUND stores results
  await bus.adapters.storage.set({ lastAnalysis: pageData })

  // 5. Update SIGNALS (syncs to all contexts)
  settings.value = { ...settings.value, lastAnalysisTime: Date.now() }

  // 6. Show results in popup UI
  displayResults(pageData)
})

// The OPTIONS page automatically shows updated timestamp
// The SIDE PANEL shows the analysis in its activity log
// The DEVTOOLS panel can inspect the detailed data
```

This demonstrates the power of the unified message bus - seamless communication across all extension contexts!
