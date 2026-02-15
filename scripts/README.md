# Build Scripts

## For Framework Developers

**`../build.ts`** - Builds the framework itself (the example extension)

```bash
bun run build
```

## For Extension Users

**`build-user-extension.ts`** - Build script users can copy for their own extensions

### Usage

```bash
# Build extension at specific path
bun run scripts/build-user-extension.ts path/to/your-extension

# Build in production mode
bun run scripts/build-user-extension.ts path/to/your-extension --prod

# Build full-featured example
bun run scripts/build-user-extension.ts examples/full-featured
```

### Copy for Your Own Extension

Users can copy this script to their extension:

```bash
cp scripts/build-user-extension.ts my-extension/build.ts
cd my-extension
bun run build.ts
```

### What It Does

1. ✅ Bundles TypeScript (including framework imports)
2. ✅ Copies HTML files
3. ✅ Copies assets (icons, images, etc.)
4. ✅ Builds CSS files
5. ✅ Copies manifest.json
6. ✅ Outputs to `dist/` directory

### Requirements

Your extension should have this structure:

```
your-extension/
├── src/
│   ├── background/
│   │   └── index.ts          # Your background script
│   ├── popup/
│   │   ├── index.tsx         # Your popup UI
│   │   └── popup.html
│   ├── options/
│   │   ├── index.tsx
│   │   └── options.html
│   └── shared/
│       ├── state/            # Your state (using framework primitives)
│       └── types/            # Your types
├── manifest.json
└── build.ts                   # Copy of build-user-extension.ts
```

### Importing Framework

In your code, import framework primitives:

```typescript
// Import framework state primitives
import { $sharedState, $syncedState } from '@fairfox/web-ext/state'
import { getMessageBus } from '@fairfox/web-ext/message-bus'

// Or if framework is in parent directory:
import { $sharedState } from '../../../src/shared/lib/state'
```

The build script handles bundling everything together!
