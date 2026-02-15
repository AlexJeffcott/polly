# Building the Full-Featured Example

## Overview

The full-featured example imports from the framework source (`../../src/`).
We have two options for building it:

## Option 1: Use Framework Build (Recommended)

Since the full-featured example is just the framework + example handlers, we can reuse the framework build:

```bash
# From project root
bun run build

# Playwright uses: examples/full-featured/dist/
# But points to: dist/ (framework output)
```

**In Playwright helper:**
```typescript
export const extensionPath = path.resolve(__dirname, '../../../dist')
```

This works because:
- Full-featured example = framework + custom handlers
- Custom handlers are in framework's background (dev mode only)
- Example UI is added via query params or separate pages

## Option 2: Separate Build (If Needed Later)

If we want completely separate full-featured example:

```bash
cd examples/full-featured
bun install
bun run build
```

**Build script would:**
1. Bundle TypeScript with framework imports
2. Copy HTML files
3. Copy manifest
4. Output to `dist/`

## Current Setup

For now, use **Option 1** - the framework build already includes everything needed!

The full-featured example demonstrates how users would:
1. Import framework primitives (`$sharedState`, `getMessageBus`)
2. Add custom message handlers
3. Create reactive UIs
4. Test cross-context sync

Playwright tests validate this all works correctly.
