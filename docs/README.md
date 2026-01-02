# Documentation

Comprehensive documentation for the Chrome Extension framework with full type safety, distributed messaging, and signal synchronization.

## Core Documentation

### [ARCHITECTURE.md](./ARCHITECTURE.md)
Overview of the system architecture, including:
- Extension context structure
- Message flow patterns
- Component relationships
- State management

### [ADAPTERS.md](./ADAPTERS.md)
Adapter pattern implementation for browser APIs:
- All adapter interfaces (Runtime, Storage, Tabs, Window, Offscreen, ContextMenus, Fetch, Logger)
- Chrome implementations
- Mock implementations for testing
- Dependency injection patterns
- **Recently updated with Logger Adapter**

### [MESSAGING.md](./MESSAGING.md)
Distributed messaging system:
- Cross-context communication
- Message routing
- Request/response patterns
- Type-safe message definitions

### [STATE.md](./STATE.md) ⭐ NEW
Reactive state management with sync and persistence:
- State primitives ($sharedState, $syncedState, $persistedState, $state)
- Automatic synchronization across contexts
- Lamport clock for conflict resolution
- Runtime validation and deep equality
- Best practices and patterns
- **Complete rewrite with proper versioning and validation**

### [TESTING.md](./TESTING.md) ⭐ NEW
Comprehensive testing guide:
- Test architecture and patterns
- Mock adapter usage
- Unit vs integration testing
- Common testing patterns
- Best practices
- **Complete guide with all learnings from achieving 100% type safety**

### [LOGGING.md](./LOGGING.md) ⭐ NEW
Logger adapter for consistent, testable logging:
- LoggerAdapter interface and implementations
- Production ConsoleLoggerAdapter
- MockLogger for tests (silent by default)
- Structured logging with context
- Integration with MessageBus adapters
- Best practices and migration guide

### [ERRORS.md](./ERRORS.md) ⭐ NEW
Type-safe error handling system:
- Custom error classes with metadata
- ErrorCode enum for categorization
- Error propagation through message bus
- Error recovery patterns (retry, fallback, graceful degradation)
- User-facing error messages
- Testing error scenarios

### [TECHNICAL.md](./TECHNICAL.md)
Step-by-step implementation guide:
- Background message router
- Signal synchronization
- Build system configuration
- Context implementations
- Development workflow

### [BUILD.md](./BUILD.md)
Build system and tooling:
- Bun configuration
- TypeScript setup
- Watch mode
- Production builds

## Verification & Formal Methods

### [OPTIMIZATION.md](./OPTIMIZATION.md)
TLA+ verification optimization guide:
- Tier 1 optimizations (zero precision loss)
- Tier 2 optimizations (controlled approximations)
- Message filtering and symmetry reduction
- Per-message bounds and temporal constraints
- Performance impact and best practices

### [TLA_RESOURCES.md](./TLA_RESOURCES.md) ⭐ NEW
Comprehensive TLA+ learning resources:
- Official documentation and tools
- Interactive tutorials and courses
- Community blogs and forums
- Symmetry reduction guides
- Troubleshooting and FAQs
- Related formal methods tools

## Quick Start

1. **New to the project?** Start with [ARCHITECTURE.md](./ARCHITECTURE.md)
2. **Building a feature?** See [TECHNICAL.md](./TECHNICAL.md)
3. **Writing tests?** Check [TESTING.md](./TESTING.md)
4. **Working with adapters?** Read [ADAPTERS.md](./ADAPTERS.md)
5. **Message passing?** Study [MESSAGING.md](./MESSAGING.md)
6. **Error handling?** See [ERRORS.md](./ERRORS.md)
7. **Logging?** Check [LOGGING.md](./LOGGING.md)
8. **Verification & TLA+?** See [OPTIMIZATION.md](./OPTIMIZATION.md) and [TLA_RESOURCES.md](./TLA_RESOURCES.md)

## Key Achievements

✅ **100% Type Safety** - Zero `as any` casts in test code
✅ **126 Tests Passing** - Comprehensive unit and integration tests
✅ **Adapter Pattern** - All external APIs wrapped for testability
✅ **Dependency Injection** - All services support optional dependencies
✅ **Path Aliases** - Clean imports with `@/` throughout codebase
✅ **Mock Infrastructure** - Complete mock implementations mirroring production
✅ **Lazy Initialization** - Avoid chrome undefined errors
✅ **Signal Synchronization** - Cross-context state management

## Testing Summary

```bash
bun test                              # Run all tests
bun test tests/unit/                  # Unit tests only
bun test tests/integration/           # Integration tests only
bun test -t "MessageBus"              # Tests matching pattern
```

**Current Coverage:**
- Unit tests for all adapters ✅
- Unit tests for message bus ✅
- Unit tests for message router ✅
- Unit tests for background handlers ✅
- Unit tests for signal synchronization ✅
- Integration tests for cross-context communication ✅
- Zero type casts in test code ✅

## Architecture Highlights

### Adapter Pattern
Every external API (Chrome APIs, fetch, etc.) is wrapped in an adapter interface:
```typescript
// Production
const adapters = createChromeAdapters()

// Testing
const adapters = createMockAdapters()
```

### Message Bus
Type-safe cross-context communication:
```typescript
// Send
const response = await bus.send({ type: 'SETTINGS_GET' })

// Handle
bus.on('SETTINGS_GET', async (payload) => {
  return { settings: await getSettings() }
})
```

### Signal Synchronization
Automatic state sync across contexts:
```typescript
const count = syncedSignal(0, {
  key: 'counter',
  broadcast: true
})

// Updates automatically propagate to all contexts
count.value++
```

## Best Practices

1. **Use path aliases** - Import with `@/` not `../../`
2. **Inject dependencies** - All services accept optional adapters/bus
3. **Create mocks directly** - When you need access to mock internals
4. **No type casts** - Use properly typed mocks instead
5. **Lazy initialization** - Don't call chrome APIs at module level
6. **Spy before connecting** - Avoid infinite loops in port tests
7. **Share mock instances** - For integration tests with shared state

## Contributing

When adding new features:
1. Add adapter interface if using external APIs
2. Create corresponding mock implementation
3. Write unit tests for business logic
4. Write integration tests for cross-context behavior
5. Update relevant documentation
6. Use path aliases for all imports

## Recent Updates

- ✨ Added [LOGGING.md](./LOGGING.md) with Logger Adapter pattern and MockLogger
- ✨ Added [ERRORS.md](./ERRORS.md) with type-safe error handling system
- 🔧 Updated [ADAPTERS.md](./ADAPTERS.md) to include Logger Adapter as 8th adapter type
- 🧪 Updated [TESTING.md](./TESTING.md) with MockLogger usage patterns
- ✨ Added [TESTING.md](./TESTING.md) with comprehensive test patterns
- 🔧 Updated [ADAPTERS.md](./ADAPTERS.md) with FetchAdapter and modern mock patterns
- 🚀 Achieved 100% type safety with zero `as any` casts
- 📦 Implemented path alias system using `@/`
- 🧪 Created mirror mock directory structure in `tests/helpers/adapters/`
- 🔌 Applied adapter pattern to fetch API
- 💉 Added dependency injection to all background services
