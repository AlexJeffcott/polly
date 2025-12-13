# Imported Type Guard Detection - Implementation

## Overview

This enhancement extends v0.3.1's type guard detection to support **imported type guard functions**. Previously, only type guards defined in the same file as the if/else-if chain were detected. Now, Polly follows imports automatically using ts-morph's symbol resolution.

## What's New

### Before (v0.3.1)

Only detected type guards in the same file:

```typescript
// ✅ Detected
function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

if (isQueryMessage(message)) {
  handleQuery(message)
}
```

```typescript
// ❌ NOT detected
import { isQueryMessage } from './messages'

if (isQueryMessage(message)) {
  handleQuery(message)
}
```

### After (v0.3.2)

Detects type guards from imports:

```typescript
// Type guard defined in: packages/api/src/ws/messages.ts
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

// Used in: packages/api/src/server.ts
import { isQueryMessage } from '@ws/messages'

if (isQueryMessage(message)) {
  handleQuery(message)  // ✅ NOW DETECTED!
}
```

## Implementation Details

### How It Works

1. **Check local type guards first** (fast path)
2. **If not found**, use ts-morph's `getDefinitionNodes()` to resolve the import
3. **Analyze the imported function** for type predicate return type
4. **Extract message type** using existing logic

### Code Changes

**File:** `packages/polly/vendor/analysis/src/extract/handlers.ts`

**New Method:** `resolveImportedTypeGuard(identifier)`
- Uses ts-morph symbol resolution
- Automatically handles path aliases (`@ws/`, relative paths)
- Reuses existing message type extraction logic
- Returns `null` on resolution errors (graceful degradation)

**Modified Method:** `extractHandlerFromIfClause()`
- Now tries local type guards first (performance)
- Falls back to import resolution if not found locally
- Maintains same return signature (backward compatible)

## Benefits

✅ **No manual import parsing** - ts-morph handles all the complexity
✅ **Path alias support** - Works with `@ws/`, `@/`, etc. automatically
✅ **Relative imports** - Handles `./`, `../` correctly
✅ **Performance** - ts-morph caches symbol resolution
✅ **Graceful errors** - Skips resolution failures silently
✅ **100% backward compatible** - Existing code works identically

## Supported Patterns

### Pattern 1: Named Imports
```typescript
import { isQueryMessage, isCommandMessage } from './messages'

if (isQueryMessage(msg)) { ... }
```

### Pattern 2: Path Aliases
```typescript
import { isQueryMessage } from '@ws/messages'
import { isCommandMessage } from '@/types/guards'

if (isQueryMessage(msg)) { ... }
```

### Pattern 3: Relative Imports
```typescript
import { isQueryMessage } from '../shared/messages'
import { isCommandMessage } from './guards'

if (isQueryMessage(msg)) { ... }
```

### Pattern 4: Chained Imports
```typescript
import { isQueryMessage } from './messages'

if (isQueryMessage(msg)) {
  handleQuery(msg)
} else if (isCommandMessage(msg)) {
  handleCommand(msg)
}
```

## Limitations

### What's NOT Supported

1. **External package imports** - Only local project files are analyzed
   ```typescript
   import { something } from 'external-package'  // Skipped
   ```

2. **Circular imports** - May cause resolution issues (handled gracefully)

3. **Dynamic imports** - Only static imports are supported
   ```typescript
   const { isQuery } = await import('./messages')  // Not detected
   ```

4. **Re-exports** - Direct exports only
   ```typescript
   // This works:
   export function isQuery(...): msg is Query { ... }

   // This might not work:
   export { isQuery } from './other-file'
   ```

## Testing

### Lingua CMS Integration Test

**Type guards file:** `packages/api/src/ws/messages.ts`
```typescript
export function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}
export function isCommandMessage(msg: RequestMessage): msg is CommandMessage {
  return msg.type === 'command'
}
export function isSubscribeMessage(msg: RequestMessage): msg is SubscribeMessage {
  return msg.type === 'subscribe'
}
export function isUnsubscribeMessage(msg: RequestMessage): msg is UnsubscribeMessage {
  return msg.type === 'unsubscribe'
}
```

**Usage file:** `packages/api/src/server.ts`
```typescript
import { isQueryMessage, isCommandMessage, isSubscribeMessage, isUnsubscribeMessage } from '@ws/messages'

if (isQueryMessage(message)) {
  response = await handleQuery(message, wsData.user)
} else if (isCommandMessage(message)) {
  response = await handleCommand(message, wsData.user)
} else if (isSubscribeMessage(message)) {
  response = await handleSubscribe(ws, wsData, message)
} else if (isUnsubscribeMessage(message)) {
  response = await handleUnsubscribe(ws, wsData, message)
}
```

**Expected Result:**
```
✓ Found 1 context(s)
✓ Found 4 message flow(s)  ← NEW!
✓ Found 38 integration(s)

Contexts:
  • server
    - 4 handler(s)  ← NEW!
      * query
      * command
      * subscribe
      * unsubscribe
```

## Performance Impact

- **Minimal** - Symbol resolution is only attempted when local lookup fails
- **Cached** - ts-morph caches all symbol resolutions internally
- **Fast path** - Local type guards are checked first (no resolution needed)

## Migration

No migration needed! This is a pure enhancement:
- Existing projects work identically
- New patterns are detected automatically
- No configuration changes required
- No breaking changes

## Future Enhancements

Potential improvements for future versions:

1. **Re-export support** - Follow export chains
2. **Type alias detection** - Handle `type Guards = typeof isQuery`
3. **Namespace imports** - Support `import * as guards from './messages'`
4. **Performance metrics** - Track resolution cache hits/misses

## Related

- Issue #4: Enhancement request
- PR #3: Initial type guard detection (v0.3.1)
- Issue #2: Original type guard pattern request
