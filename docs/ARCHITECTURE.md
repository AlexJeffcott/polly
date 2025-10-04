# Chrome Extension Architecture

## Overview

This framework provides a scalable, type-safe architecture for Chrome extensions that leverages all execution contexts with distributed, event-driven communication using Preact Signals.

## Technology Stack

- **Runtime**: Bun
- **Language**: TypeScript (100% type safety)
- **UI Framework**: Preact + Preact Signals
- **Styling**: CSS Modules
- **Testing**: Playwright + Bun Test
- **Linting/Formatting**: Biome
- **Build**: Custom `build.ts` using Bun APIs

## Execution Contexts

Chrome extensions run in **7 distinct execution contexts**, each with different capabilities and lifecycle:

### Singleton Contexts (max 1 instance per extension)

#### 1. Background (Service Worker)
- **Lifecycle**: Persistent (event-driven, can sleep)
- **Capabilities**:
  - Full Chrome API access
  - Cross-origin requests (no CORS)
  - Context menu management
  - Message routing hub
  - Long-lived connections
- **Cannot**:
  - Access DOM
  - Use canvas/audio APIs
- **Purpose**: Central coordinator, API client, message router

#### 2. Popup (0-1 instances)
- **Lifecycle**: Ephemeral (closes on blur)
- **Capabilities**:
  - Chrome APIs (most)
  - Preact UI
  - Can message background/content
- **Cannot**:
  - Access page DOM
  - Make cross-origin requests
- **Purpose**: Quick settings, actions, status display

#### 3. Options Page (0-1 instances)
- **Lifecycle**: Tab-based (standard web page)
- **Capabilities**:
  - Chrome APIs
  - Preact UI
  - Full page layout
- **Cannot**:
  - Access page DOM
- **Purpose**: Settings, preferences, configuration

#### 4. Offscreen Document (0-1 instances)
- **Lifecycle**: Created/destroyed on demand
- **Capabilities**:
  - DOM APIs (canvas, audio, clipboard)
  - No visible UI
  - Background-like but with document
- **Cannot**:
  - Show UI to user
- **Purpose**: DOM-dependent operations for background (clipboard, canvas, audio)

### Per-Tab Contexts (N instances, one per tab)

#### 5. Content Script
- **Lifecycle**: Per tab (injected on page load)
- **Capabilities**:
  - Read/write page DOM
  - Some Chrome APIs
  - CSS injection
  - Message to background
- **Cannot**:
  - Access page's JavaScript (window variables, functions)
  - Make cross-origin requests
- **Purpose**: DOM manipulation, page content bridge

#### 6. Page Script
- **Lifecycle**: Per tab (injected by content script)
- **Capabilities**:
  - Full access to page's JavaScript environment
  - Call page functions
  - Access page variables (window.*)
- **Cannot**:
  - Use Chrome APIs
  - Directly message background
- **Purpose**: Access page's JavaScript, call page functions, read page state

#### 7. DevTools Panel
- **Lifecycle**: Per tab with DevTools open
- **Capabilities**:
  - Chrome DevTools APIs
  - Preact UI
  - Access inspected tab
  - Message to background
- **Cannot**:
  - Directly access page DOM
- **Purpose**: Inspection UI, debugging interface, developer tools

## Architecture Pattern: Hub and Spoke

```
                         ┌─────────────────────┐
                         │    Background       │
                         │  (Service Worker)   │
                         │                     │
                         │  • Message Router   │
                         │  • API Client       │
                         │  • Context Menus    │
                         │  • Port Manager     │
                         └──────────┬──────────┘
                                   │
              ┌────────────────────┼────────────────────┐
              │                    │                    │
         ┌────▼─────┐         ┌────▼─────┐      ┌──────▼────────┐
         │  Popup   │         │ Options  │      │  Offscreen    │
         │  (0-1)   │         │  Page    │      │  Document     │
         │          │         │  (0-1)   │      │  (0-1)        │
         └──────────┘         └──────────┘      └───────────────┘
                                   │
        ┌──────────────────────────┴──────────────────────────┐
        │                          │                          │
   ┌────▼─────┐              ┌─────▼─────┐            ┌──────▼──────┐
   │  TAB 1   │              │  TAB 2    │            │   TAB N     │
   ├──────────┤              ├───────────┤            ├─────────────┤
   │ DevTools │              │ DevTools  │            │  DevTools   │
   │  Panel   │              │  Panel    │            │   Panel     │
   │(if open) │              │ (if open) │            │  (if open)  │
   ├──────────┤              ├───────────┤            ├─────────────┤
   │ Content  │              │  Content  │            │   Content   │
   │  Script  │              │   Script  │            │   Script    │
   │    ▲     │              │     ▲     │            │      ▲      │
   │    │postMessage         │     │     │            │      │      │
   │    ▼     │              │     ▼     │            │      ▼      │
   │   Page   │              │    Page   │            │     Page    │
   │  Script  │              │   Script  │            │    Script   │
   └──────────┘              └───────────┘            └─────────────┘
```

## Communication Patterns

### 1. Request/Response Pattern
One-off messages for single actions:
```
DevTools → Background → Content Script → Response
```

### 2. Broadcast Pattern
One-to-many for state synchronization:
```
Background → ALL Contexts (DevTools, Popup, Content Scripts)
```

### 3. Long-Lived Connections
Persistent channels for high-frequency communication:
```
DevTools ↔ Background (persistent port)
Content Script ↔ Background (persistent port)
```

### 4. Window Message Bridge
Content Script ↔ Page Script communication:
```
Content Script ↔ window.postMessage ↔ Page Script
```

## Message Routing

### Background as Smart Router

The Background context acts as the central message router:

1. **Tracks all connections**:
   - Map of `tabId → Content Script Port`
   - Map of `tabId → DevTools Panel Port`
   - Reference to `Popup Port` (0-1)
   - Reference to `Offscreen Port` (0-1)

2. **Routes messages**:
   - Target-specific (tabId required for per-tab contexts)
   - Broadcast to all contexts
   - Response correlation (match responses to requests)

3. **Manages lifecycle**:
   - Port connections/disconnections
   - Tab creation/removal
   - Context cleanup

### Message Flow Examples

#### Example 1: DevTools queries DOM in inspected tab
```
┌──────────┐         ┌──────────┐         ┌──────────┐
│ DevTools │         │Background│         │ Content  │
│ (Tab 2)  │         │  Router  │         │ (Tab 2)  │
└─────┬────┘         └─────┬────┘         └─────┬────┘
      │                    │                    │
      │ DOM_QUERY (tab:2)  │                    │
      ├───────────────────>│                    │
      │                    │  DOM_QUERY         │
      │                    ├───────────────────>│
      │                    │                    │
      │                    │     Response       │
      │                    │<───────────────────┤
      │     Response       │                    │
      │<───────────────────┤                    │
      │                    │                    │
```

#### Example 2: Context menu action
```
┌──────────┐         ┌──────────┐         ┌──────────┐
│   User   │         │Background│         │ Content  │
│ (Tab 3)  │         │          │         │ (Tab 3)  │
└─────┬────┘         └─────┬────┘         └─────┬────┘
      │                    │                    │
      │  Right-click menu  │                    │
      ├───────────────────>│                    │
      │                    │  DOM_UPDATE        │
      │                    ├───────────────────>│
      │                    │                    │
      │                    │  Execute + Respond │
      │                    │<───────────────────┤
      │                    │                    │
      │                    │  STATE_SYNC        │
      │                    ├───────────────────>│ (Broadcast
      │                    ├───────────────────>│  to ALL
      │                    ├───────────────────>│  contexts)
```

#### Example 3: Offscreen clipboard operation
```
┌──────────┐         ┌──────────┐         ┌──────────┐
│  Popup   │         │Background│         │Offscreen │
└─────┬────┘         └─────┬────┘         └─────┬────┘
      │                    │                    │
      │ CLIPBOARD_WRITE    │                    │
      ├───────────────────>│                    │
      │                    │ Ensure offscreen   │
      │                    │ document exists    │
      │                    │                    │
      │                    │  CLIPBOARD_WRITE   │
      │                    ├───────────────────>│
      │                    │                    │
      │                    │  navigator.        │
      │                    │  clipboard.write() │
      │                    │                    │
      │                    │     Response       │
      │                    │<───────────────────┤
      │     Response       │                    │
      │<───────────────────┤                    │
```

## State Management: Distributed Signals

> **📖 Complete Documentation:** See [STATE.md](./STATE.md) for comprehensive state management guide.

### State Primitives

The framework provides four state primitives with automatic synchronization and persistence:

#### 1. `$state()` - Local Signals
Reactive state within a single context (UI-only):
```typescript
const isLoading = $state(false)
const selectedTab = $state('elements')
```

#### 2. `$syncedState()` - Synced Signals
Synchronized across contexts but NOT persisted:
```typescript
const activeTab = $syncedState('active-tab', null)
```

#### 3. `$persistedState()` - Persisted Signals
Persisted to storage but NOT synced (context-specific):
```typescript
const popupState = $persistedState('popup:collapsed', false)
```

#### 4. `$sharedState()` - Synced + Persisted
Synchronized across ALL contexts AND persisted to storage:
```typescript
const settings = $sharedState('app-settings', {
  theme: 'dark',
  notifications: true
})
```

### State Synchronization Flow

```
Context A: settings.value = newValue
    ↓
    ├─ Increment Lamport clock (5 → 6)
    ├─ Write to chrome.storage
    └─ Broadcast STATE_SYNC message
        ↓
Background Router: Route to all contexts
        ↓
Context B, C, D:
    ├─ Validate clock (accept if newer)
    ├─ Validate value (if validator provided)
    ├─ Check deep equality (skip if same)
    └─ Update local signal
        ↓
Preact re-renders reactively
```

**Features:**
- Lamport clock for conflict resolution
- Runtime validation
- Deep equality checks
- Debounce support
- Eventually consistent

See [STATE.md](./STATE.md) for complete API reference, best practices, and examples.

## Type Safety Strategy

### 1. Discriminated Union of All Messages
```typescript
type ExtensionMessage =
  | { type: 'DOM_QUERY'; selector: string }
  | { type: 'API_REQUEST'; endpoint: string; method: string }
  | { type: 'CLIPBOARD_WRITE'; text: string }
  // ... all possible messages
```

### 2. Response Type Inference
```typescript
type MessageResponse<T extends ExtensionMessage> =
  T extends { type: 'DOM_QUERY' } ? { elements: Element[] } :
  T extends { type: 'API_REQUEST' } ? { data: unknown; status: number } :
  // ... responses for each message type
```

### 3. Typed Message Bus
```typescript
async send<T extends ExtensionMessage>(
  payload: T
): Promise<MessageResponse<T>>
// Return type automatically inferred from payload type!
```

### 4. Context-Specific Handlers
```typescript
// Messages can only be handled by appropriate contexts
type MessageHandler = {
  'DOM_QUERY': 'content'
  'API_REQUEST': 'background'
  'CLIPBOARD_WRITE': 'offscreen'
  // ... routing table
}
```

## Adapter Pattern

To decouple from Chrome APIs and enable testing, all browser APIs are wrapped in thin adapters:

```
Application Code
      ↓
  Adapters (Interface)
      ↓
Chrome API Implementation
```

**Benefits**:
- Testable (mock adapters)
- Browser-agnostic (could support Firefox)
- Type-safe
- Traceable (logging in adapters)

## Project Structure

```
/src
  /background           # Service Worker
    index.ts            # Entry point
    message-router.ts   # Routes messages between contexts
    api-client.ts       # External API calls
    context-menu.ts     # Context menu registration

  /content              # Content Script (per tab)
    index.ts            # Entry point
    dom-operations.ts   # DOM read/write
    page-bridge.ts      # Bridge to page script
    styles.module.css   # Isolated styles

  /page                 # Page Script (injected)
    index.ts            # Access page's JS environment

  /devtools             # DevTools Panel (per tab)
    index.ts            # Register panel
    panel.tsx           # Panel UI (Preact)
    panel.html
    panel.module.css

  /popup                # Popup (0-1)
    index.tsx           # Popup UI (Preact)
    popup.html
    popup.module.css

  /options              # Options Page (0-1)
    index.tsx           # Settings UI (Preact)
    options.html
    options.module.css

  /offscreen            # Offscreen Document (0-1)
    index.ts            # DOM APIs for background
    offscreen.html

  /shared               # Shared code
    /types
      messages.ts       # Message type definitions
      state.ts          # State schemas
      manifest.ts       # Manifest types

    /lib
      message-bus.ts    # Typed messaging layer
      state.ts          # State primitives (sync + persistence)
      errors.ts         # Custom errors

    /adapters
      index.ts          # Adapter factory
      runtime.adapter.ts    # Runtime adapter interface
      storage.adapter.ts    # Storage adapter interface
      tabs.adapter.ts       # Tabs adapter interface
      window.adapter.ts     # Window adapter interface
      /chrome
        runtime.chrome.ts   # Chrome runtime implementation
        storage.chrome.ts   # Chrome storage implementation
        tabs.chrome.ts      # Chrome tabs implementation
        window.chrome.ts    # Chrome window implementation
      /mock
        runtime.mock.ts     # Mock for testing
        storage.mock.ts     # Mock for testing

  /components           # Shared Preact components
    /ui
      Button.tsx
      Input.tsx
      Panel.tsx

/docs
  ARCHITECTURE.md       # This file
  MESSAGING.md          # Messaging system details
  ADAPTERS.md           # Adapter pattern details
  TECHNICAL.md          # Implementation guide

/tests
  /unit
  /e2e                  # Playwright tests

build.ts                # Bun build script
manifest.ts             # Generate manifest.json
biome.json              # Biome configuration
tsconfig.json           # TypeScript configuration
```

## Design Principles

### 1. Type Safety First
Every message, response, and handler is fully typed. No `any` types in the public API.

### 2. Explicit Over Implicit
Message routing is explicit (specify target context). No magic.

### 3. Single Responsibility
Each context has a clear purpose. Background doesn't do DOM work, Content Script doesn't make API calls.

### 4. Fail Fast
Invalid messages cause compile-time errors, not runtime failures.

### 5. Testable
Adapters allow dependency injection. Every context can be unit tested.

### 6. Performance Conscious
- Long-lived ports for high-frequency communication
- Selective signal synchronization (opt-in)
- Lazy loading of contexts (offscreen created on demand)

### 7. Developer Experience
- Auto-complete for all message types
- Type inference for responses
- Clear error messages
- Hot reload during development

## Security Considerations

### 1. Content Security Policy
Service worker enforces strict CSP. No inline scripts.

### 2. Message Validation
All messages validated at runtime (zod schemas).

### 3. Origin Checking
Page script messages verify `event.source === window`.

### 4. Minimal Permissions
Only request necessary Chrome permissions.

### 5. Isolated Worlds
Content script runs in isolated world, cannot be accessed by page scripts.

## Build System

Custom `build.ts` using Bun:
- Bundles all contexts separately
- CSS Modules transformation
- Source maps for debugging
- Watch mode for development
- Production optimization
- Manifest generation with types

## Next Steps

See individual documentation files for implementation details:
- [MESSAGING.md](./MESSAGING.md) - Type-safe messaging implementation
- [ADAPTERS.md](./ADAPTERS.md) - Adapter pattern details
- [TECHNICAL.md](./TECHNICAL.md) - Step-by-step implementation guide
