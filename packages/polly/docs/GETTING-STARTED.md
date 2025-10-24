# Getting Started with @fairfox/web-ext Framework

This guide walks you through setting up a new extension project with the web-ext framework.

## Prerequisites

- Node.js 18+ or Bun
- TypeScript knowledge
- Basic understanding of Chrome extension architecture

## Quick Start

### 1. Install Dependencies

```bash
# Using npm
npm install @fairfox/web-ext @preact/signals-core

# Using bun
bun add @fairfox/web-ext @preact/signals-core
```

### 2. TypeScript Configuration

Create `tsconfig.json`:

```json
{
  "compilerOptions": {
    "target": "ES2020",
    "module": "ESNext",
    "lib": ["ES2020", "DOM"],
    "moduleResolution": "bundler",
    "strict": true,
    "skipLibCheck": true,
    "esModuleInterop": true,
    "forceConsistentCasingInFileNames": true,
    "noEmit": true,

    // Path aliases (optional but recommended)
    "baseUrl": ".",
    "paths": {
      "@/*": ["./src/*"]
    },

    // Chrome extension types
    "types": ["chrome"]
  },
  "include": ["src/**/*"],
  "exclude": ["node_modules", "dist"]
}
```

### 3. Project Structure

```
my-extension/
├── src/
│   ├── background/
│   │   └── index.ts          # Background script
│   ├── content/
│   │   └── index.ts          # Content script
│   ├── popup/
│   │   └── index.ts          # Popup UI
│   ├── shared/
│   │   ├── types/
│   │   │   └── messages.ts   # Custom message types
│   │   └── state/
│   │       └── app-state.ts  # Shared state
│   └── manifest.json
├── tsconfig.json
└── package.json
```

## Basic Usage

### Define Custom Messages

Create `src/shared/types/messages.ts`:

```typescript
import type { ExtensionMessage } from '@fairfox/web-ext/types'

// Define your custom messages
export type MyCustomMessages =
  | { type: "FETCH_DATA"; url: string }
  | { type: "UPDATE_UI"; data: unknown }
  | { type: "SAVE_SETTINGS"; settings: Record<string, any> }

// Combine with framework messages
export type AllMessages = ExtensionMessage | MyCustomMessages
```

### Background Script

Create `src/background/index.ts`:

```typescript
import { createContext } from '@fairfox/web-ext'

const bus = createContext('background', {
  async onInit(bus) {
    // Register your message handlers
    bus.registerHandlers({
      FETCH_DATA: async (payload) => {
        const response = await fetch(payload.url)
        const data = await response.json()
        return { success: true, data }
      },

      SAVE_SETTINGS: async (payload) => {
        await bus.adapters.storage.set(payload.settings)
        return { success: true }
      },
    })
  },
  onError(error) {
    console.error('Background error:', error)
  }
})
```

### Content Script

Create `src/content/index.ts`:

```typescript
import { createContext } from '@fairfox/web-ext'

const bus = createContext('content', {
  async onInit(bus) {
    // Register handlers
    bus.registerHandlers({
      UPDATE_UI: async (payload) => {
        // Update page UI
        document.body.dataset.updated = 'true'
        return { success: true }
      }
    })

    // Send message to background
    const result = await bus.sendToBackground({
      type: 'FETCH_DATA',
      url: 'https://api.example.com/data'
    })

    if (result.success) {
      // Use the data
      console.log('Fetched data:', result.data)
    }
  }
})
```

### Popup

Create `src/popup/index.ts`:

```typescript
import { createContext } from '@fairfox/web-ext'

const bus = createContext('popup', {
  async onInit(bus) {
    // Setup UI
    document.getElementById('save-btn')?.addEventListener('click', async () => {
      const settings = {
        theme: 'dark',
        enabled: true
      }

      const result = await bus.sendToBackground({
        type: 'SAVE_SETTINGS',
        settings
      })

      if (result.success) {
        bus.helpers.closePopup()
      }
    })
  }
})
```

## Import Strategies

### Strategy 1: Path Aliases (Recommended)

**Pros:** Clean imports, easy to refactor
**Cons:** Requires bundler configuration

```typescript
import { createContext } from '@/shared/lib/context-helpers'
import { getMessageBus } from '@/shared/lib/message-bus'
```

**Setup:**
```json
// tsconfig.json
{
  "compilerOptions": {
    "paths": {
      "@/*": ["./src/*"]
    }
  }
}

// Your bundler (webpack/vite/etc) also needs configuration
```

### Strategy 2: Package Exports (Future)

Once published to npm with proper exports:

```typescript
import { createContext, getMessageBus } from '@fairfox/web-ext'
```

### Strategy 3: Relative Imports

**Pros:** No configuration needed
**Cons:** Verbose, harder to refactor

```typescript
import { createContext } from '../shared/lib/context-helpers'
import { getMessageBus } from '../shared/lib/message-bus'
```

## Bundler Configuration

### Using Vite

```typescript
// vite.config.ts
import { defineConfig } from 'vite'
import { resolve } from 'path'

export default defineConfig({
  resolve: {
    alias: {
      '@': resolve(__dirname, './src')
    }
  },
  build: {
    rollupOptions: {
      input: {
        background: 'src/background/index.ts',
        content: 'src/content/index.ts',
        popup: 'src/popup/index.html'
      },
      output: {
        entryFileNames: '[name]/index.js'
      }
    }
  }
})
```

### Using Bun

```typescript
// build.ts
await Bun.build({
  entrypoints: [
    './src/background/index.ts',
    './src/content/index.ts',
    './src/popup/index.ts'
  ],
  outdir: './dist',
  target: 'browser',
  format: 'esm',
  splitting: true
})
```

## Manifest Configuration

Create `src/manifest.json`:

```json
{
  "manifest_version": 3,
  "name": "My Extension",
  "version": "1.0.0",
  "description": "My awesome extension",

  "background": {
    "service_worker": "background/index.js",
    "type": "module"
  },

  "content_scripts": [
    {
      "matches": ["<all_urls>"],
      "js": ["content/index.js"]
    }
  ],

  "action": {
    "default_popup": "popup/index.html"
  },

  "permissions": [
    "storage",
    "tabs"
  ],

  "host_permissions": [
    "https://*/*"
  ]
}
```

## Testing

The framework provides built-in test utilities:

```typescript
import { createTestSuite } from '@fairfox/web-ext'

const tests = createTestSuite('popup', bus)

tests.add('fetch data works', async () => {
  const result = await bus.sendToBackground({
    type: 'FETCH_DATA',
    url: 'https://api.example.com/test'
  })
  return result.success
})

await tests.run()
tests.printResults()
```

## Next Steps

- See [DX-IMPROVEMENTS.md](./DX-IMPROVEMENTS.md) for advanced features
- Check out [example-extension](../tests/framework-validation/example-extension) for complete examples
- Read about [context-specific helpers](./DX-IMPROVEMENTS.md#5-context-specific-helpers)

## Common Issues

### TypeScript can't find modules

**Problem:** `Cannot find module '@/shared/lib/...'`

**Solution:** Configure `tsconfig.json` with proper path mappings:
```json
{
  "compilerOptions": {
    "baseUrl": ".",
    "paths": {
      "@/*": ["./src/*"]
    }
  }
}
```

### Chrome types not found

**Problem:** `Property 'chrome' does not exist`

**Solution:** Install Chrome types:
```bash
npm install -D @types/chrome
```

### Imports work in IDE but fail at runtime

**Problem:** TypeScript path aliases work in IDE but bundler doesn't resolve them

**Solution:** Configure your bundler (Vite, Webpack, etc.) to resolve the same aliases

## Support

- GitHub Issues: [github.com/fairfox/web-ext](https://github.com/fairfox/web-ext)
- Examples: See `tests/framework-validation/example-extension`
