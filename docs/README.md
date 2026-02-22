# Documentation

Documentation for the `@fairfox/polly` multi-execution-context framework.

## Core Documentation

### [ADAPTERS.md](./ADAPTERS.md)
Adapter pattern implementation for browser and platform APIs:
- All adapter interfaces (Runtime, Storage, Tabs, Window, Offscreen, ContextMenus, Fetch, Logger)
- Chrome, Web, Node, and Mock implementations
- Dependency injection patterns

### [MESSAGING.md](./MESSAGING.md)
Distributed messaging system:
- Cross-context communication
- Message routing
- Request/response patterns
- Type-safe message definitions

### [STATE.md](./STATE.md)
Reactive state management with sync and persistence:
- State primitives ($sharedState, $syncedState, $persistedState, $state)
- Automatic synchronization across contexts
- Lamport clock for conflict resolution
- Runtime validation and deep equality

### [ERRORS.md](./ERRORS.md)
Type-safe error handling system:
- Custom error classes with metadata
- ErrorCode enum for categorization
- Error propagation through message bus
- Error recovery patterns

### [LOGGING.md](./LOGGING.md)
Logger adapter for consistent, testable logging:
- LoggerAdapter interface and implementations
- MockLogger for tests
- Structured logging with context
- Integration with MessageBus adapters

### [BACKGROUND_SETUP.md](./BACKGROUND_SETUP.md)
Background script initialization:
- `createBackground()` vs `getMessageBus()`
- MessageRouter singleton pattern
- Double-execution protection

### [TESTING.md](./TESTING.md)
Testing guide:
- Mock adapter usage
- Unit vs integration testing patterns
- Best practices

### [DX-IMPROVEMENTS.md](./DX-IMPROVEMENTS.md)
Developer experience enhancements:
- `createContext()` helper
- `registerHandlers()` bulk registration
- Context-specific helpers

### [MIGRATION-DX-ENHANCEMENTS.md](./MIGRATION-DX-ENHANCEMENTS.md)
Migration guide for v0.13 DX enhancements:
- Verification tracking with `{ verify: true }`
- Runtime constraints
- Auto-persistence
- Shape validation helpers

## Verification & Formal Methods

### [TLA_RESOURCES.md](./TLA_RESOURCES.md)
Curated TLA+ learning resources:
- Official documentation and tools
- Tutorials and courses
- Symmetry reduction guides
- Troubleshooting and FAQs

## Generated Artifacts

### [architecture.dsl](./architecture.dsl)
Auto-generated Structurizr DSL from `polly visualize`.

## Quick Start

1. **New to the project?** Start with the root [README.md](../README.md)
2. **Writing tests?** Check [TESTING.md](./TESTING.md)
3. **Working with adapters?** Read [ADAPTERS.md](./ADAPTERS.md)
4. **Message passing?** Study [MESSAGING.md](./MESSAGING.md)
5. **State management?** See [STATE.md](./STATE.md)
6. **Error handling?** See [ERRORS.md](./ERRORS.md)
7. **Verification & TLA+?** See [TLA_RESOURCES.md](./TLA_RESOURCES.md)
