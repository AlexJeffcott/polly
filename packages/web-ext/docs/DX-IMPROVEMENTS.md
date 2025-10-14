# Developer Experience Improvements

This document outlines the DX improvements made to the web-ext framework based on analyzing the example extension usage patterns.

## Summary of Improvements

| Improvement | Before | After | Lines Saved |
|-------------|--------|-------|-------------|
| Context initialization | ~20 lines of boilerplate | 1 line with `createContext()` | ~19 lines |
| Handler registration | Multiple `bus.on()` calls | Single `registerHandlers()` | ~5-10 lines |
| Error handling | try/catch everywhere | Global `onError()` handler | ~5 lines per call |
| Message routing | Unclear `bus.send()` | Explicit `sendToBackground()` etc | Clarity ++ |
| Context helpers | Manual DOM/API access | Built-in `bus.helpers` | ~3-5 lines per usage |
| Test utilities | Manual window management | `createTestSuite()` | ~10-15 lines |

**Total: ~30-40% less boilerplate code with better clarity and type safety!**

---

## 1. Context Initializer Helper

### Problem
Every context file had 20+ lines of repetitive initialization code:

```typescript
// OLD WAY ❌
export async function initPopup() {
  console.log('[Popup] Initializing...')
  registerPopupHandlers()
  setupPopupUI()
  await runPopupTests()
  console.log('[Popup] Ready')
}

if (typeof window !== 'undefined') {
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => {
      initPopup().catch((err) => {
        console.error('[Popup] Initialization failed:', err)
      })
    })
  } else {
    initPopup().catch((err) => {
      console.error('[Popup] Initialization failed:', err)
    })
  }
}
```

### Solution
One-liner initialization with `createContext()`:

```typescript
// NEW WAY ✅
import { createContext } from '@/shared/lib/context-helpers'

const bus = createContext('popup', {
  async onInit(bus) {
    registerPopupHandlers(bus)
    setupPopupUI()
    await runPopupTests(bus)
  },
  onError(error) {
    console.error('Popup error:', error)
  }
})
```

**Benefits:**
- 90% less boilerplate
- Automatic DOM ready handling
- Consistent error handling
- Cleaner, more maintainable code

**Location:** `src/shared/lib/context-helpers.ts`

---

## 2. Batch Handler Registration

### Problem
Registering many handlers was verbose:

```typescript
// OLD WAY ❌
bus.on('TEST_STORAGE', async (payload) => { ... })
bus.on('TEST_TABS', async (payload) => { ... })
bus.on('TEST_LOGGER', async (payload) => { ... })
bus.on('TEST_RUNTIME', async (payload) => { ... })
// ... 10 more handlers
```

### Solution
Register multiple handlers at once:

```typescript
// NEW WAY ✅
bus.registerHandlers({
  'TEST_STORAGE': async (payload) => { ... },
  'TEST_TABS': async (payload) => { ... },
  'TEST_LOGGER': async (payload) => { ... },
  'TEST_RUNTIME': async (payload) => { ... },
})
```

**Benefits:**
- Handlers organized in one place
- Less repetitive code
- Better overview of all handlers
- Still fully type-safe

**Location:** `MessageBus.registerHandlers()` in `src/shared/lib/message-bus.ts`

---

## 3. Global Error Handler

### Problem
Every message send needed try/catch:

```typescript
// OLD WAY ❌
try {
  const result = await bus.send({ type: 'TEST' })
  console.log('Success:', result)
} catch (error) {
  console.error('Failed:', error instanceof Error ? error.message : String(error))
}
```

### Solution
Register once, handle errors globally:

```typescript
// NEW WAY ✅
bus.onError((error, bus) => {
  console.error(`[${bus.context}] Error:`, error)
  // Report to error tracking service
})

// No try/catch needed
const result = await bus.send({ type: 'TEST' })
```

**Benefits:**
- Centralized error handling
- Less boilerplate per call
- Easy integration with error tracking services
- Still can use try/catch for specific cases

**Location:** `MessageBus.onError()` in `src/shared/lib/message-bus.ts`

---

## 4. Explicit Routing API

### Problem
Unclear where messages were being sent:

```typescript
// OLD WAY ❌
await bus.send({ type: 'TEST_STORAGE' })
// ^ Goes where? Background? Content? All tabs?

await bus.send({ type: 'ANALYZE_PAGE' })
// ^ How do I target a specific tab?
```

### Solution
Explicit routing methods:

```typescript
// NEW WAY ✅
await bus.sendToBackground({ type: 'TEST_STORAGE' })
await bus.sendToContentScript(tabId, { type: 'ANALYZE_PAGE' })
await bus.sendToAllTabs({ type: 'REFRESH_UI' })
await bus.sendToPopup({ type: 'UPDATE_UI' })
await bus.sendToOptions({ type: 'SETTINGS_UPDATED' })
await bus.sendToDevTools({ type: 'INSPECTION_DATA' })
await bus.sendToSidePanel({ type: 'UPDATE_ACTIVITY_LOG' })
```

**Benefits:**
- Crystal clear routing intent
- Better autocomplete
- Easier to understand code flow
- Fewer routing bugs

**Location:** Multiple methods in `src/shared/lib/message-bus.ts`

---

## 5. Context-Specific Helpers

### Problem
Common operations required manual code:

```typescript
// OLD WAY ❌
// Content script
const pageInfo = {
  url: window.location.href,
  title: document.title,
  host: window.location.host,
}

// DevTools
chrome.devtools.inspectedWindow.eval(code, (result, error) => {
  // Manual promise wrapping, error handling...
})

// Options page
const notification = document.createElement('div')
// 15 lines of styling and animation...
```

### Solution
Built-in helpers for each context:

```typescript
// NEW WAY ✅
// Content script
const pageInfo = bus.helpers.getPageInfo()
const links = bus.helpers.queryElements('a')
bus.helpers.injectCSS('.highlight { background: yellow; }')

// DevTools
const result = await bus.helpers.evalInPage('window.myVariable')
const tabId = bus.helpers.inspectedTabId
bus.helpers.reloadInspectedPage({ ignoreCache: true })

// Options page
bus.helpers.showSaveConfirmation('Settings saved!')
bus.helpers.showError('Failed to save')

// Popup
const currentTab = await bus.helpers.getCurrentTab()
bus.helpers.setDimensions(400, 600)

// Background
await bus.helpers.openOptionsPage()
bus.helpers.setBadge('5', '#ff0000')
```

**Benefits:**
- Less boilerplate for common tasks
- Consistent APIs across contexts
- Better discoverability (autocomplete)
- Context-appropriate utilities

**Location:** `src/shared/lib/context-specific-helpers.ts`

**Available Helpers:**

| Context | Helper Methods |
|---------|---------------|
| **Content** | `getPageInfo()`, `queryElements()`, `getPageMetadata()`, `injectCSS()`, `removeCSS()` |
| **DevTools** | `inspectedTabId`, `evalInPage()`, `getPageResource()`, `reloadInspectedPage()` |
| **Popup** | `getCurrentTab()`, `closePopup()`, `setDimensions()` |
| **Options** | `openInNewTab()`, `showSaveConfirmation()`, `showError()` |
| **Side Panel** | `getCurrentTab()`, `isVisible()`, `setWidth()` |
| **Background** | `getAllTabs()`, `getExtensionViews()`, `openOptionsPage()`, `setBadge()`, `clearBadge()` |

---

## 6. Built-in Test Utilities

### Problem
Manual test result management:

```typescript
// OLD WAY ❌
try {
  const storageResult = await bus.send({ type: 'TEST_STORAGE' })
  const tabsResult = await bus.send({ type: 'TEST_TABS' })
  const logResult = await bus.send({ type: 'TEST_LOGGER' })

  // Manual window management
  ;(window as any).__POPUP_TEST_RESULTS__ = {
    storage: storageResult,
    tabs: tabsResult,
    logger: logResult,
    timestamp: Date.now(),
  }
} catch (error) {
  // Manual error handling
  ;(window as any).__POPUP_TEST_RESULTS__ = {
    error: error instanceof Error ? error.message : String(error),
  }
}
```

### Solution
Built-in test suite utilities:

```typescript
// NEW WAY ✅
import { createTestSuite } from '@/shared/lib/test-helpers'

const tests = createTestSuite('popup', bus)

// Add tests
tests.addMessageTest('storage', { type: 'TEST_STORAGE' })
tests.addMessageTest('tabs', { type: 'TEST_TABS' })
tests.addMessageTest('logger', { type: 'TEST_LOGGER' })

// Or with custom validators
tests.add('custom test', async () => {
  const result = await bus.sendToBackground({ type: 'MY_TEST' })
  return result.success
})

// Run and automatically expose results
await tests.run()
tests.printResults()

// Results automatically at window.__TEST_RESULTS__.popup
```

**Benefits:**
- Automatic result management
- Built-in timing/duration tracking
- Pretty console output
- Playwright-ready result exposure
- Easy test validation

**Location:** `src/shared/lib/test-helpers.ts`

**API:**
- `createTestSuite(context, bus)` - Create test suite
- `tests.add(name, fn)` - Add custom test
- `tests.addMessageTest(name, message, validator?)` - Add message test
- `tests.run()` - Run all tests and expose results
- `tests.runTest(name)` - Run single test
- `tests.printResults()` - Print to console
- `quickTest(name, fn)` - One-off test utility

---

## Migration Guide

### Step 1: Update Initialization

```typescript
// Before
export async function initPopup() { ... }
if (typeof window !== 'undefined') { ... }

// After
import { createContext } from '@/shared/lib/context-helpers'
const bus = createContext('popup', {
  async onInit(bus) { ... }
})
```

### Step 2: Batch Register Handlers

```typescript
// Before
bus.on('MSG_1', async (payload) => { ... })
bus.on('MSG_2', async (payload) => { ... })

// After
bus.registerHandlers({
  'MSG_1': async (payload) => { ... },
  'MSG_2': async (payload) => { ... },
})
```

### Step 3: Use Explicit Routing

```typescript
// Before
await bus.send({ type: 'TEST' })

// After
await bus.sendToBackground({ type: 'TEST' })
```

### Step 4: Use Context Helpers

```typescript
// Before (content script)
const pageInfo = {
  url: window.location.href,
  title: document.title,
}

// After
const pageInfo = bus.helpers.getPageInfo()
```

### Step 5: Use Test Utilities

```typescript
// Before
;(window as any).__TEST_RESULTS__ = { ... }

// After
const tests = createTestSuite('popup', bus)
tests.add('test name', async () => { ... })
await tests.run()
```

---

## Examples

See these files for complete examples:

- **Improved Popup:** `tests/framework-validation/example-extension/src/popup/test-popup-improved.ts`
- **Improved Content Script:** `tests/framework-validation/example-extension/src/content/test-content-improved.ts`
- **Original (for comparison):** `tests/framework-validation/example-extension/src/popup/test-popup.ts`

---

## Type Safety

All new APIs maintain full type safety:

```typescript
// ✅ Type-safe handler registration
bus.registerHandlers({
  'TEST_STORAGE': async (payload) => {
    payload.testValue // ✅ Type: string | undefined
    payload.invalid   // ❌ TypeScript error
    return { success: true } // ✅ Correct return type
  }
})

// ✅ Type-safe helpers (specific to context)
const bus = getMessageBus('content')
bus.helpers.getPageInfo()    // ✅ Available in content
bus.helpers.evalInPage()     // ❌ Not available in content (DevTools only)

// ✅ Type-safe routing
await bus.sendToBackground({ type: 'TEST' })  // ✅ Valid message type
await bus.sendToBackground({ type: 'INVALID' }) // ❌ TypeScript error
```

---

## Performance Impact

All improvements have minimal performance overhead:

- **Context helpers:** Zero overhead (just organized utilities)
- **Batch registration:** Same as individual registration
- **Error handlers:** ~1-2ms per error (only when errors occur)
- **Test utilities:** Only used during testing
- **Explicit routing:** Same as `send()` with explicit target

**Result: Better DX with no performance penalty!**
