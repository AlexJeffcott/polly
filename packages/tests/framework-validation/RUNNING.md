# Running Framework Validation Tests

## Quick Start

```bash
# Build framework
bun run build

# Run DOM-based tests
bun run test:framework

# Run with UI (see tests visually)
bun run test:framework:ui

# Run in headed mode (see browser)
bun run test:framework:headed

# Debug specific test
bun run test:framework:debug
```

## What Gets Tested

### ✅ State Management
- `$sharedState` - Cross-context sync + persistence
- `$syncedState` - Cross-context sync (no persistence)
- Local `signal` - Context-specific (no sync)

### ✅ Reactivity
- DOM updates automatically on signal changes
- Preact renders correctly
- UI responds to user interactions

### ✅ Cross-Context Synchronization
- Popup → Options sync
- Options → Popup sync
- Multiple contexts see same values
- Updates propagate automatically

### ✅ Persistence
- State survives page reload
- Storage adapter works correctly

### ✅ Message Bus
- Cross-context messaging
- Message routing
- Request/response pattern

### ✅ Adapters
- Storage, Tabs, Runtime, etc.
- All work with real Chrome APIs

## Test Structure

```typescript
// 1. Open extension pages
const popup = await openPopup(context, extensionId)
const options = await openOptions(context, extensionId)

// 2. Interact with DOM
await popup.click('[data-testid="increment-counter"]')

// 3. Validate DOM updates (reactivity)
expect(await popup.locator('[data-testid="test-counter"]').textContent()).toBe('1')

// 4. Validate cross-context sync
expect(await options.locator('[data-testid="options-counter"]').textContent()).toBe('1')
```

## Current Setup

The tests use the framework's built output (`dist/`) with test mode enabled via query params:
- `popup.html?test-mode=true` - Shows test UI
- `options.html?test-mode=true` - Shows test UI

This proves the framework works without polluting the source code!

## Test Results

Each test validates a specific aspect:

1. **State reactivity** - UI updates on signal changes ✅
2. **Cross-context sync** - Popup ↔ Options ✅
3. **Persistence** - Reload and verify ✅
4. **Message routing** - Cross-context messages ✅
5. **Full integration** - All features together ✅

## Debugging

If tests fail:

1. **Run in headed mode** to see what's happening:
   ```bash
   bun run test:framework:headed
   ```

2. **Check extension console** in Chrome DevTools

3. **Verify build output**:
   ```bash
   ls -la dist/
   ```

4. **Run single test**:
   ```bash
   bunx playwright test tests/framework-validation/dom-based.spec.ts -g "counter increments"
   ```

## Next Steps

To test more features:

1. **Content script testing** - Add content script test UI
2. **Offscreen testing** - Test offscreen document
3. **Performance testing** - Measure message latency
4. **Edge cases** - Test error handling, timeouts, etc.

## Success Criteria

✅ All tests pass
✅ Cross-context sync works
✅ Persistence works
✅ Reactivity works
✅ No type errors
✅ No console errors
✅ Framework is clean (no test code in src/)

**Result: Framework is production ready!**
