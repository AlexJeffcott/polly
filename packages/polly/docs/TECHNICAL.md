# Technical Implementation Guide

## Overview

This guide provides step-by-step implementation details for building the Chrome extension framework with complete type safety, distributed messaging, and signal synchronization.

## Table of Contents

1. [Background Message Router](#1-background-message-router)
2. [Signal Synchronization](#2-signal-synchronization)
3. [Build System](#3-build-system)
4. [Context Implementations](#4-context-implementations)
5. [Testing Strategy](#5-testing-strategy)
6. [Development Workflow](#6-development-workflow)

---

## 1. Background Message Router

The Background context acts as the central hub for all messaging. It tracks connections from all contexts and routes messages accordingly.

### Implementation

```typescript
// src/background/message-router.ts

import { getMessageBus } from '../shared/lib/message-bus'
import type { RoutedMessage, RoutedResponse, Context } from '../shared/types/messages'
import type { PortAdapter } from '../shared/adapters'

export class MessageRouter {
  private bus = getMessageBus('background')

  // Track connections by context and tab
  private contentPorts = new Map<number, PortAdapter>()      // tabId → Port
  private devtoolsPorts = new Map<number, PortAdapter>()     // tabId → Port
  private popupPort: PortAdapter | null = null
  private optionsPort: PortAdapter | null = null
  private offscreenPort: PortAdapter | null = null

  constructor() {
    this.setupPortConnections()
    this.setupTabListeners()
    this.setupMessageHandlers()
  }

  private setupPortConnections(): void {
    this.bus.adapters.runtime.onConnect((port) => {
      console.log(`[Background] Port connected: ${port.name}`)

      // Parse port name to determine context and tab
      const [context, tabIdStr] = port.name.split('-')

      switch (context) {
        case 'content':
          const contentTabId = parseInt(tabIdStr)
          this.contentPorts.set(contentTabId, port)
          port.onDisconnect(() => {
            console.log(`[Background] Content port disconnected for tab ${contentTabId}`)
            this.contentPorts.delete(contentTabId)
          })
          break

        case 'devtools':
          const devtoolsTabId = parseInt(tabIdStr)
          this.devtoolsPorts.set(devtoolsTabId, port)
          port.onDisconnect(() => {
            console.log(`[Background] DevTools port disconnected for tab ${devtoolsTabId}`)
            this.devtoolsPorts.delete(devtoolsTabId)
          })
          break

        case 'popup':
          this.popupPort = port
          port.onDisconnect(() => {
            console.log(`[Background] Popup disconnected`)
            this.popupPort = null
          })
          break

        case 'options':
          this.optionsPort = port
          port.onDisconnect(() => {
            console.log(`[Background] Options disconnected`)
            this.optionsPort = null
          })
          break

        case 'offscreen':
          this.offscreenPort = port
          port.onDisconnect(() => {
            console.log(`[Background] Offscreen disconnected`)
            this.offscreenPort = null
          })
          break
      }

      // Handle messages from this port
      port.onMessage((message: RoutedMessage | RoutedResponse) => {
        if ('success' in message) {
          // This is a response, route back to original sender
          this.routeResponse(message)
        } else {
          // This is a request, route to target
          this.routeMessage(message)
        }
      })
    })
  }

  private setupTabListeners(): void {
    // Clean up ports when tabs are closed
    this.bus.adapters.tabs.onRemoved((tabId) => {
      console.log(`[Background] Tab ${tabId} removed, cleaning up ports`)
      this.contentPorts.delete(tabId)
      this.devtoolsPorts.delete(tabId)
    })

    // Track tab updates
    this.bus.adapters.tabs.onUpdated((tabId, changeInfo, tab) => {
      if (changeInfo.status === 'complete') {
        console.log(`[Background] Tab ${tabId} loaded: ${tab.url}`)
      }
    })
  }

  private setupMessageHandlers(): void {
    // Handle messages that need routing
    this.bus.adapters.runtime.onMessage((message: RoutedMessage | RoutedResponse, sender, sendResponse) => {
      if ('success' in message) {
        this.routeResponse(message)
      } else {
        this.routeMessage(message).then(sendResponse)
      }
      return true
    })
  }

  private async routeMessage(message: RoutedMessage): Promise<any> {
    console.log(`[Background] Routing message: ${message.payload.type} from ${message.source} to ${message.target}`)

    if (message.target === 'broadcast') {
      return this.broadcast(message)
    }

    // Route to specific context
    switch (message.target) {
      case 'background':
        // Message is for background, let MessageBus handle it
        return

      case 'content':
        if (!message.tabId) {
          console.error('[Background] Content target requires tabId')
          return { success: false, error: 'tabId required for content target' }
        }
        const contentPort = this.contentPorts.get(message.tabId)
        if (contentPort) {
          contentPort.postMessage(message)
        } else {
          console.error(`[Background] No content script port for tab ${message.tabId}`)
          return { success: false, error: 'Content script not connected' }
        }
        break

      case 'devtools':
        if (!message.tabId) {
          console.error('[Background] DevTools target requires tabId')
          return { success: false, error: 'tabId required for devtools target' }
        }
        const devtoolsPort = this.devtoolsPorts.get(message.tabId)
        if (devtoolsPort) {
          devtoolsPort.postMessage(message)
        } else {
          console.error(`[Background] No DevTools port for tab ${message.tabId}`)
          return { success: false, error: 'DevTools not connected' }
        }
        break

      case 'popup':
        if (this.popupPort) {
          this.popupPort.postMessage(message)
        } else {
          console.error('[Background] Popup not connected')
          return { success: false, error: 'Popup not connected' }
        }
        break

      case 'options':
        if (this.optionsPort) {
          this.optionsPort.postMessage(message)
        } else {
          console.error('[Background] Options not connected')
          return { success: false, error: 'Options not connected' }
        }
        break

      case 'offscreen':
        if (this.offscreenPort) {
          this.offscreenPort.postMessage(message)
        } else {
          console.error('[Background] Offscreen not connected')
          return { success: false, error: 'Offscreen not connected' }
        }
        break

      case 'page':
        // Page script is not directly connected to background
        // Must route through content script
        if (!message.tabId) {
          console.error('[Background] Page target requires tabId')
          return { success: false, error: 'tabId required for page target' }
        }
        const contentPortForPage = this.contentPorts.get(message.tabId)
        if (contentPortForPage) {
          contentPortForPage.postMessage(message)
        } else {
          console.error(`[Background] No content script to forward to page in tab ${message.tabId}`)
          return { success: false, error: 'Content script not connected' }
        }
        break
    }
  }

  private routeResponse(response: RoutedResponse): void {
    // Responses are handled by MessageBus automatically via pending requests
    console.log(`[Background] Routing response for message ${response.id}`)
  }

  private broadcast(message: RoutedMessage): void {
    console.log(`[Background] Broadcasting message: ${message.payload.type}`)

    // Send to all content scripts
    for (const [tabId, port] of this.contentPorts.entries()) {
      try {
        port.postMessage(message)
      } catch (error) {
        console.error(`[Background] Failed to broadcast to content script in tab ${tabId}`, error)
      }
    }

    // Send to all DevTools panels
    for (const [tabId, port] of this.devtoolsPorts.entries()) {
      try {
        port.postMessage(message)
      } catch (error) {
        console.error(`[Background] Failed to broadcast to DevTools in tab ${tabId}`, error)
      }
    }

    // Send to popup if open
    if (this.popupPort) {
      try {
        this.popupPort.postMessage(message)
      } catch (error) {
        console.error('[Background] Failed to broadcast to popup', error)
      }
    }

    // Send to options if open
    if (this.optionsPort) {
      try {
        this.optionsPort.postMessage(message)
      } catch (error) {
        console.error('[Background] Failed to broadcast to options', error)
      }
    }

    // Send to offscreen if exists
    if (this.offscreenPort) {
      try {
        this.offscreenPort.postMessage(message)
      } catch (error) {
        console.error('[Background] Failed to broadcast to offscreen', error)
      }
    }
  }

  // Public API for sending messages from background
  async sendToTab(tabId: number, message: RoutedMessage): Promise<void> {
    const port = this.contentPorts.get(tabId)
    if (port) {
      port.postMessage(message)
    } else {
      throw new Error(`No content script connected to tab ${tabId}`)
    }
  }

  async sendToDevTools(tabId: number, message: RoutedMessage): Promise<void> {
    const port = this.devtoolsPorts.get(tabId)
    if (port) {
      port.postMessage(message)
    } else {
      throw new Error(`No DevTools connected to tab ${tabId}`)
    }
  }

  broadcastToAll(message: RoutedMessage): void {
    this.broadcast(message)
  }

  // Status queries
  isContentScriptConnected(tabId: number): boolean {
    return this.contentPorts.has(tabId)
  }

  isDevToolsConnected(tabId: number): boolean {
    return this.devtoolsPorts.has(tabId)
  }

  getConnectedTabs(): number[] {
    return Array.from(this.contentPorts.keys())
  }

  getConnectedDevTools(): number[] {
    return Array.from(this.devtoolsPorts.keys())
  }
}
```

### Background Entry Point

```typescript
// src/background/index.ts

import { MessageRouter } from './message-router'
import { APIClient } from './api-client'
import { ContextMenuManager } from './context-menu'
import { SettingsManager } from './settings'
import { OffscreenManager } from './offscreen-manager'

console.log('[Background] Service worker starting...')

// Initialize router
const router = new MessageRouter()

// Initialize managers
const apiClient = new APIClient()
const contextMenu = new ContextMenuManager(router)
const settings = new SettingsManager()
const offscreen = new OffscreenManager()

// Initialize
async function init() {
  await settings.load()
  await contextMenu.setup()
  console.log('[Background] Service worker ready')
}

init().catch(console.error)

// Keep service worker alive (optional, for debugging)
chrome.runtime.onInstalled.addListener(() => {
  console.log('[Background] Extension installed/updated')
})
```

---

## 2. Signal Synchronization

Distributed signals allow reactive state management across all contexts.

### Signal Sync Implementation

```typescript
// src/shared/lib/signal-sync.ts

import { signal, Signal, effect } from '@preact/signals'
import { getMessageBus } from './message-bus'
import type { Context } from '../types/messages'

type SyncOptions = {
  persist?: boolean           // Save to chrome.storage
  storageKey?: string        // Custom storage key
  contexts?: Context[]       // Which contexts to sync to (default: all)
  debounceMs?: number       // Debounce updates
}

const syncedSignals = new Map<string, Signal<any>>()

function getCurrentContext(): Context {
  // Detect current context
  if (typeof chrome !== 'undefined' && chrome.devtools) {
    return 'devtools'
  }
  if (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.getManifest) {
    // Check if we're in background
    try {
      if (chrome.extension.getBackgroundPage() === window) {
        return 'background'
      }
    } catch {}
  }
  // Default fallback - you'd want more robust detection
  return 'content'
}

export function syncedSignal<T>(
  initialValue: T,
  options: SyncOptions = {}
): Signal<T> {
  const signalId = crypto.randomUUID()
  const sig = signal<T>(initialValue)
  const currentContext = getCurrentContext()

  syncedSignals.set(signalId, sig)

  const bus = getMessageBus(currentContext)

  // Load from storage if persist is enabled
  if (options.persist) {
    const storageKey = options.storageKey || `signal_${signalId}`
    bus.adapters.storage.get([storageKey]).then((result) => {
      if (result[storageKey] !== undefined) {
        sig.value = result[storageKey]
      }
    })
  }

  // Set up effect to broadcast changes
  let debounceTimer: NodeJS.Timeout | null = null
  effect(() => {
    const value = sig.value

    // Debounce if specified
    if (options.debounceMs) {
      if (debounceTimer) clearTimeout(debounceTimer)
      debounceTimer = setTimeout(() => {
        broadcastUpdate(signalId, value)
      }, options.debounceMs)
    } else {
      broadcastUpdate(signalId, value)
    }
  })

  function broadcastUpdate(id: string, value: any) {
    // Persist to storage
    if (options.persist) {
      const storageKey = options.storageKey || `signal_${id}`
      bus.adapters.storage.set({ [storageKey]: value })
    }

    // Broadcast to other contexts
    bus.broadcast({
      type: 'SIGNAL_UPDATE',
      signalId: id,
      value,
      source: currentContext
    })
  }

  // Listen for updates from other contexts
  bus.on('SIGNAL_UPDATE', async (payload) => {
    if (payload.signalId !== signalId) return

    // Layer 1: Ignore our own broadcasts (fast)
    if (payload.source === currentContext) {
      return
    }

    // Layer 2: Skip if data hasn't actually changed (prevents redundant updates)
    if (deepEqual(sig.value, payload.value)) {
      return
    }

    // Only update if we passed both checks
    sig.value = payload.value
  })

  return sig
}

// Simple deep equality check
function deepEqual(a: any, b: any): boolean {
  if (a === b) return true
  if (a == null || b == null) return false
  if (typeof a !== 'object' || typeof b !== 'object') return false

  const keysA = Object.keys(a)
  const keysB = Object.keys(b)

  if (keysA.length !== keysB.length) return false

  for (const key of keysA) {
    if (!keysB.includes(key)) return false
    if (!deepEqual(a[key], b[key])) return false
  }

  return true
}

// Create synced computed signal
export function syncedComputed<T>(
  compute: () => T,
  options: SyncOptions = {}
): Signal<T> {
  const computed = signal<T>(compute())

  effect(() => {
    computed.value = compute()
  })

  return syncedSignal(computed.value, options)
}

// Get signal by ID (for deserialization)
export function getSignalById(id: string): Signal<any> | undefined {
  return syncedSignals.get(id)
}
```

### Usage Example

```typescript
// shared/state/app-state.ts

import { syncedSignal } from '../lib/signal-sync'
import type { Settings } from '../types/messages'

// Synced across all contexts, persisted to storage
export const settings = syncedSignal<Settings>(
  {
    theme: 'auto',
    autoSync: true,
    debugMode: false,
    notifications: true,
    apiEndpoint: 'https://api.example.com',
    refreshInterval: 60000
  },
  {
    persist: true,
    storageKey: 'app-settings'
  }
)

// Synced but not persisted
export const currentTab = syncedSignal<number | null>(null)

// Local to each context (not synced) - use regular signal
import { signal } from '@preact/signals'
export const uiState = signal({
  sidebarOpen: false,
  selectedPanel: 'main'
})
```

```typescript
// devtools/panel.tsx

import { settings, currentTab } from '../shared/state/app-state'

export function Panel() {
  return (
    <div>
      <h1>Theme: {settings.value.theme}</h1>
      <button onClick={() => {
        // Change will automatically sync to all contexts
        settings.value = { ...settings.value, theme: 'dark' }
      }}>
        Set Dark Theme
      </button>

      <p>Current Tab: {currentTab.value}</p>
    </div>
  )
}
```

---

## 3. Build System

Custom build script using Bun APIs.

### Build Script

```typescript
// build.ts

import { rmSync, mkdirSync } from 'node:fs'
import { generateManifest } from './manifest'

const isProd = process.argv.includes('--prod')
const isWatch = process.argv.includes('--watch')

console.log(`🔨 Building extension (${isProd ? 'production' : 'development'})...`)

// Clean dist folder
try {
  rmSync('dist', { recursive: true, force: true })
} catch {}
mkdirSync('dist', { recursive: true })

// Define all entry points
const entryPoints = {
  // Background service worker
  'background/index.js': 'src/background/index.ts',

  // Content script
  'content/index.js': 'src/content/index.ts',
  'content/styles.css': 'src/content/styles.module.css',

  // Page script (injected into page)
  'page/index.js': 'src/page/index.ts',

  // DevTools
  'devtools/index.js': 'src/devtools/index.ts',
  'devtools/panel.js': 'src/devtools/panel.tsx',
  'devtools/panel.css': 'src/devtools/panel.module.css',

  // Popup
  'popup/popup.js': 'src/popup/index.tsx',
  'popup/popup.css': 'src/popup/popup.module.css',

  // Options
  'options/options.js': 'src/options/index.tsx',
  'options/options.css': 'src/options/options.module.css',

  // Offscreen
  'offscreen/offscreen.js': 'src/offscreen/index.ts',
}

// Build each entry point
async function build() {
  console.log('📦 Bundling entry points...')

  for (const [outPath, inPath] of Object.entries(entryPoints)) {
    try {
      await Bun.build({
        entrypoints: [inPath],
        outdir: 'dist',
        naming: outPath,
        target: 'browser',
        minify: isProd,
        sourcemap: isProd ? 'none' : 'inline',
        splitting: false, // Chrome extensions don't support module splitting well
        format: 'esm',
        external: ['chrome'], // Don't bundle chrome APIs
      })
      console.log(`  ✓ ${inPath} → dist/${outPath}`)
    } catch (error) {
      console.error(`  ✗ Failed to build ${inPath}:`, error)
    }
  }

  // Copy HTML files
  console.log('📄 Copying HTML files...')
  await Bun.write('dist/devtools/devtools.html', await Bun.file('src/devtools/devtools.html').text())
  await Bun.write('dist/devtools/panel.html', await Bun.file('src/devtools/panel.html').text())
  await Bun.write('dist/popup/popup.html', await Bun.file('src/popup/popup.html').text())
  await Bun.write('dist/options/options.html', await Bun.file('src/options/options.html').text())
  await Bun.write('dist/offscreen/offscreen.html', await Bun.file('src/offscreen/offscreen.html').text())

  // Generate manifest
  console.log('📝 Generating manifest.json...')
  const manifest = generateManifest(isProd)
  await Bun.write('dist/manifest.json', JSON.stringify(manifest, null, 2))

  // Copy assets
  console.log('🖼️  Copying assets...')
  try {
    await Bun.$`cp -r src/assets dist/assets`
  } catch {
    console.log('  (no assets folder found)')
  }

  console.log('✅ Build complete!')
}

// Watch mode
if (isWatch) {
  console.log('👀 Watch mode enabled...')

  const watcher = Bun.watch({
    paths: ['src'],
    onChange: async (event, path) => {
      console.log(`\n🔄 Change detected: ${path}`)
      await build()
    }
  })

  await build()
  console.log('Watching for changes...')
} else {
  await build()
}
```

### Manifest Generator

```typescript
// manifest.ts

export function generateManifest(isProd: boolean) {
  return {
    manifest_version: 3,
    name: 'Extension Name',
    version: '1.0.0',
    description: 'Extension description',

    // Background service worker
    background: {
      service_worker: 'background/index.js',
      type: 'module'
    },

    // Content scripts
    content_scripts: [
      {
        matches: ['<all_urls>'],
        js: ['content/index.js'],
        css: ['content/styles.css'],
        run_at: 'document_idle'
      }
    ],

    // DevTools
    devtools_page: 'devtools/devtools.html',

    // Action (popup)
    action: {
      default_popup: 'popup/popup.html',
      default_icon: {
        16: 'assets/icon16.png',
        48: 'assets/icon48.png',
        128: 'assets/icon128.png'
      }
    },

    // Options page
    options_page: 'options/options.html',

    // Permissions
    permissions: [
      'storage',
      'contextMenus',
      'scripting',
      'offscreen',
      'tabs'
    ],

    // Host permissions for API calls
    host_permissions: [
      'https://api.example.com/*'
    ],

    // Web accessible resources (for page script injection)
    web_accessible_resources: [
      {
        resources: ['page/index.js'],
        matches: ['<all_urls>']
      }
    ],

    // Icons
    icons: {
      16: 'assets/icon16.png',
      48: 'assets/icon48.png',
      128: 'assets/icon128.png'
    },

    // Content Security Policy (only in dev for hot reload, etc.)
    ...(!isProd && {
      content_security_policy: {
        extension_pages: "script-src 'self'; object-src 'self'"
      }
    })
  }
}
```

---

## 4. Context Implementations

### Content Script

```typescript
// src/content/index.ts

import { getMessageBus } from '../shared/lib/message-bus'
import { injectPageScript } from './page-bridge'

console.log('[Content Script] Initializing...')

const bus = getMessageBus('content')

// Get tab ID from background and connect with long-lived port
chrome.runtime.sendMessage({ type: 'GET_TAB_ID' }, (response) => {
  const tabId = response.tabId
  bus.connect(`content-${tabId}`)
  console.log(`[Content Script] Connected with tabId: ${tabId}`)
})

// Inject page script
injectPageScript()

// Register DOM operation handlers
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

console.log('[Content Script] Ready')
```

### Page Script Bridge

```typescript
// src/content/page-bridge.ts

export function injectPageScript(): void {
  const script = document.createElement('script')
  script.src = chrome.runtime.getURL('page/index.js')
  script.type = 'module'
  script.onload = () => {
    script.remove()
    console.log('[Content Script] Page script injected')
  }
  ;(document.head || document.documentElement).appendChild(script)
}
```

### Page Script

```typescript
// src/page/index.ts

import { getMessageBus } from '../shared/lib/message-bus'

console.log('[Page Script] Initializing...')

const bus = getMessageBus('page')

// Register handlers for page JS environment access
bus.on('PAGE_EVAL', async (payload) => {
  try {
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

console.log('[Page Script] Ready')
```

### DevTools

```typescript
// src/devtools/index.ts

// Register DevTools panel
chrome.devtools.panels.create(
  'Extension Panel',
  'assets/icon48.png',
  'devtools/panel.html',
  (panel) => {
    console.log('[DevTools] Panel created')
  }
)
```

```typescript
// src/devtools/panel.tsx

import { render } from 'preact'
import { signal } from '@preact/signals'
import { getMessageBus } from '../shared/lib/message-bus'

const bus = getMessageBus('devtools')
const tabId = chrome.devtools.inspectedWindow.tabId

// Connect with long-lived port
bus.connect(`devtools-${tabId}`)

const elements = signal<any[]>([])

async function queryDOM() {
  const response = await bus.send(
    { type: 'DOM_QUERY', selector: '.data-item' },
    { tabId }
  )
  elements.value = response.elements
}

function Panel() {
  return (
    <div>
      <h1>DevTools Panel</h1>
      <button onClick={queryDOM}>Query DOM</button>

      <ul>
        {elements.value.map((el, i) => (
          <li key={i}>
            &lt;{el.tag}&gt;: {el.text}
          </li>
        ))}
      </ul>
    </div>
  )
}

render(<Panel />, document.getElementById('root')!)
```

### Offscreen Document

```typescript
// src/offscreen/index.ts

import { getMessageBus } from '../shared/lib/message-bus'

console.log('[Offscreen] Initializing...')

const bus = getMessageBus('offscreen')

// Connect with port
bus.connect('offscreen')

// Register clipboard handlers
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

console.log('[Offscreen] Ready')
```

### Offscreen Manager (Background)

```typescript
// src/background/offscreen-manager.ts

import { adapters } from '../shared/adapters'

export class OffscreenManager {
  private isCreated = false

  async ensureOffscreenDocument(): Promise<void> {
    if (this.isCreated) return

    try {
      await adapters.offscreen.createDocument({
        url: 'offscreen/offscreen.html',
        reasons: ['CLIPBOARD'],
        justification: 'Access clipboard for copy/paste operations'
      })
      this.isCreated = true
      console.log('[Background] Offscreen document created')
    } catch (error) {
      console.error('[Background] Failed to create offscreen document:', error)
    }
  }

  async closeOffscreenDocument(): Promise<void> {
    if (!this.isCreated) return

    try {
      await adapters.offscreen.closeDocument()
      this.isCreated = false
      console.log('[Background] Offscreen document closed')
    } catch (error) {
      console.error('[Background] Failed to close offscreen document:', error)
    }
  }
}
```

---

## 5. Testing Strategy

### Unit Tests

```typescript
// tests/unit/message-bus.test.ts

import { describe, test, expect, beforeEach } from 'bun:test'
import { MessageBus } from '../../src/shared/lib/message-bus'
import { createMockAdapters } from '../../src/shared/adapters/mock'

describe('MessageBus', () => {
  let adapters: ReturnType<typeof createMockAdapters>
  let bus: MessageBus

  beforeEach(() => {
    adapters = createMockAdapters()
    bus = new MessageBus('popup', adapters)
  })

  test('should send message', async () => {
    await bus.send({ type: 'SETTINGS_GET' })
    expect(adapters.runtime.sentMessages).toHaveLength(1)
  })

  test('should handle message', async () => {
    let received = false
    bus.on('SETTINGS_UPDATE', async () => {
      received = true
      return { settings: {} as any }
    })

    adapters.runtime.simulateMessage({
      id: '1',
      source: 'background',
      target: 'popup',
      timestamp: Date.now(),
      payload: { type: 'SETTINGS_UPDATE', settings: {} as any }
    }, {})

    await new Promise(resolve => setTimeout(resolve, 10))
    expect(received).toBe(true)
  })
})
```

### E2E Tests with Playwright

```typescript
// tests/e2e/extension.test.ts

import { test, expect, chromium } from '@playwright/test'
import path from 'node:path'

test.describe('Extension E2E', () => {
  test('extension loads correctly', async () => {
    const pathToExtension = path.join(__dirname, '../../dist')
    const context = await chromium.launchPersistentContext('', {
      headless: false,
      args: [
        `--disable-extensions-except=${pathToExtension}`,
        `--load-extension=${pathToExtension}`,
      ],
    })

    const page = await context.newPage()
    await page.goto('https://example.com')

    // Wait for content script to load
    await page.waitForTimeout(1000)

    // Check that extension is loaded
    const title = await page.title()
    expect(title).toBeTruthy()

    await context.close()
  })
})
```

---

## 6. Development Workflow

### Package.json Scripts

```json
{
  "scripts": {
    "dev": "bun run build.ts --watch",
    "build": "bun run build.ts",
    "build:prod": "bun run build.ts --prod",
    "test": "bun test",
    "test:watch": "bun test --watch",
    "test:e2e": "playwright test",
    "lint": "biome check src",
    "lint:fix": "biome check --apply src",
    "format": "biome format --write src"
  }
}
```

### Development Flow

```bash
# 1. Start watch mode
bun run dev

# 2. In Chrome: chrome://extensions
# 3. Enable "Developer mode"
# 4. Click "Load unpacked"
# 5. Select the /dist folder

# Changes will auto-rebuild
# Manually reload extension in Chrome after rebuild
```

### Testing Flow

```bash
# Run unit tests
bun test

# Run unit tests in watch mode
bun test --watch

# Run E2E tests
bun test:e2e
```

### Production Build

```bash
# Build for production
bun run build:prod

# Zip for distribution
cd dist && zip -r ../extension.zip . && cd ..

# Upload extension.zip to Chrome Web Store
```

---

## Summary

This framework provides:

✅ **Complete type safety** across all contexts
✅ **Distributed messaging** with automatic routing
✅ **Reactive state management** with synced signals (two-layer protection)
✅ **Adapter pattern** for testability and decoupling
✅ **Modern build system** with Bun
✅ **Full testing** support (unit + E2E)
✅ **Offscreen document** support for clipboard operations
✅ **Context menu** integration
✅ **DevTools panel** with reactive UI

All contexts can communicate seamlessly while maintaining separation of concerns and complete type safety.
