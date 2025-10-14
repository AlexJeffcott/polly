# Minimal Example

The simplest possible @fairfox/web-ext extension. Perfect for getting started!

## What It Does

- Displays a counter in the popup
- State automatically syncs across all extension contexts
- State persists across browser restarts
- Just **3 files**, ~30 lines of code

## Quick Start

```bash
# Install dependencies
bun install

# Build extension
bun run build

# Output in dist/ - load in Chrome
```

Then:
1. Open Chrome → Extensions → Enable "Developer mode"
2. Click "Load unpacked" → Select `dist/` folder
3. Click the extension icon → See the counter!

## File Structure

```
src/
├── background/
│   └── index.ts          # 7 lines - Extension setup
├── popup/
│   ├── popup.html        # 11 lines - HTML template
│   └── index.tsx         # 20 lines - React UI
└── shared/
    └── state.ts          # 3 lines - Shared state
```

## How It Works

### 1. Define Shared State

```typescript
// src/shared/state.ts
import { $sharedState } from '@fairfox/web-ext/state'

export const counter = $sharedState('counter', 0)
```

### 2. Use in UI

```typescript
// src/popup/index.tsx
import { counter } from '../shared/state'

function Popup() {
  return (
    <div>
      <p>Count: {counter.value}</p>
      <button onClick={() => counter.value++}>
        Increment
      </button>
    </div>
  )
}
```

### 3. That's It!

- ✅ State automatically syncs everywhere
- ✅ UI updates when state changes (reactive)
- ✅ Persists across restarts
- ✅ No boilerplate, no configuration

## Try It Out

Open multiple extension pages:
- Click extension icon (popup)
- Right-click → Inspect → Switch to extension context
- Open `chrome://extensions` → Click "Details" → "Extension options"

Change the counter in one place → **instantly appears everywhere!**

## Next Steps

- See `examples/typed-messages/` for type-safe message passing
- See `examples/with-content-script/` for injecting into web pages
- Read the [full documentation](../../docs/) for all features
