# Mock Adapters

This directory contains mock implementations of all adapter interfaces defined in `src/shared/adapters/`.

## Architecture

Each mock file corresponds to a production adapter interface:

```
src/shared/adapters/runtime.adapter.ts  ←→  tools/test/src/adapters/runtime.mock.ts
src/shared/adapters/storage.adapter.ts  ←→  tools/test/src/adapters/storage.mock.ts
src/shared/adapters/tabs.adapter.ts     ←→  tools/test/src/adapters/tabs.mock.ts
...
```

## Usage

### Basic: Complete Adapter Set

```typescript
import { createMockAdapters } from '@fairfox/polly/test'

const adapters = createMockAdapters()
const bus = new MessageBus('background', adapters)
// All adapters are now properly mocked
```

### Advanced: Access Mock Internals

```typescript
import { createMockAdapters, type MockFetch } from '@fairfox/polly/test'

const adapters = createMockAdapters()
const mockFetch = adapters.fetch as MockFetch

// Queue a mock response
mockFetch._responses.push({
  status: 200,
  json: async () => ({ data: 'test' })
})

// Check calls made
expect(mockFetch._calls[0].input).toBe('https://api.example.com')
```

### Alternative: Chrome-like Grouping

Some tests need direct access to internal mock state across multiple adapters:

```typescript
import { createMockChrome } from '@fairfox/polly/test'

const mockChrome = createMockChrome()
// Returns { runtime, storage: { local }, tabs }

// Direct access to internal state
mockChrome.tabs._tabs.set(1, { id: 1, url: '...' })
mockChrome.runtime._messageListeners.forEach(...)
```

## Pattern

Each mock follows this pattern:

### 1. Mock Interface Extends Real Interface

```typescript
export interface MockRuntime extends RuntimeAdapter {
  _messageListeners: Set<...>  // Test helpers prefixed with _
  _connectListeners: Set<...>
}
```

### 2. Factory Function

```typescript
export function createMockRuntime(): MockRuntime {
  return {
    // Implement all RuntimeAdapter methods
    sendMessage: async (message) => { /* mock behavior */ },
    onMessage: (callback) => { /* mock behavior */ },

    // Test helpers for internal state inspection
    _messageListeners: messageListeners,
  }
}
```

### 3. Full Interface Compliance

TypeScript enforces that mocks implement the complete adapter interface. If an adapter interface changes, the mock breaks at compile time.

## Adding a New Mock

When adding a new adapter to production:

1. Create `new-adapter.mock.ts` in this directory
2. Define `MockNewAdapter extends NewAdapter` interface
3. Add test helpers as needed (prefix with `_`)
4. Implement factory function `createMockNewAdapter()`
5. Export from `index.ts`:
   ```typescript
   export { createMockNewAdapter, type MockNewAdapter }
   ```
6. Add to `createMockAdapters()`:
   ```typescript
   return {
     // ... existing adapters
     newAdapter: createMockNewAdapter(),
   }
   ```

## Key Principles

1. **Type Safety**: No `as any` - mocks extend real interfaces
2. **Independence**: Only import types from production, not implementations
3. **Testability**: Expose internal state via `_prefixed` properties
4. **Consistency**: Same pattern across all mocks
5. **Maintainability**: One file per adapter, mirroring production structure

## Benefits

- **Compile-time verification**: Interface changes break tests immediately
- **No mock drift**: TypeScript enforces interface compliance
- **Clear organization**: Know exactly where each mock lives
- **Easy to extend**: Follow the pattern for new adapters
- **Zero runtime dependencies**: Mocks work in any test environment (Bun, Node, etc.)

## See Also

- [Production adapters](../../../src/shared/adapters/)
- [Adapter pattern documentation](../../../docs/TECHNICAL.md)
- [Testing learnings](../../../learnings.md)
