# Full-Featured Example

This extension demonstrates how to build a production-ready extension with the @fairfox/polly framework.

## Structure

```
full-featured/
├── src/
│   ├── background/        # Background script with custom handlers
│   ├── popup/             # Popup UI with test interface
│   ├── options/           # Options UI with test interface
│   └── shared/
│       ├── state/         # Custom state using framework primitives
│       └── types/         # Custom types
├── manifest.json          # Extension manifest
├── web-ext.config.ts      # Build configuration
└── package.json           # Dependencies and scripts
```

## Usage Pattern

### 1. Install Framework

```bash
bun add @fairfox/polly
```

### 2. Import Framework Primitives

```typescript
// src/shared/state/my-state.ts
import { $sharedState, $syncedState } from '@fairfox/polly/state'

export const counter = $sharedState('counter', 0)
export const message = $syncedState('message', '')
```

### 3. Use in Components

```typescript
// src/popup/index.tsx
import { getMessageBus } from '@fairfox/polly/message-bus'
import { counter } from '../shared/state/my-state'

const bus = getMessageBus('popup')

function Popup() {
  return (
    <div>
      <div>Count: {counter.value}</div>
      <button onClick={() => counter.value++}>
        Increment
      </button>
    </div>
  )
}
```

### 4. Add Message Handlers

```typescript
// src/background/index.ts
import { createBackground } from '@fairfox/polly/background'
import { requires, ensures } from '@fairfox/polly/verify'

const { bus } = createBackground<AllMessages>()

bus.on('MY_CUSTOM_MESSAGE', async (payload) => {
  requires(/* precondition */, 'Precondition description')
  // Handle message
  ensures(/* postcondition */, 'Postcondition description')
  return { success: true }
})
```

### 5. Build

```bash
bun run build        # Development build
bun run build:prod   # Production build
```

## What This Demonstrates

This example extension demonstrates:

- ✅ Framework can be used as a package
- ✅ CLI tool works correctly
- ✅ Imports resolve properly
- ✅ State primitives work
- ✅ Message bus works
- ✅ Cross-context sync works
- ✅ Persistence works
- ✅ Reactivity works

## Building

```bash
# From full-featured directory
bun run build

# Or from framework root
bun run build:full-featured
```

Output goes to `dist/` directory, ready to load in Chrome.

## Testing

The Playwright tests load this built extension and validate all features work.
