# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.7] - 2025-12-14

### Fixed

#### Visualization: Component Diagrams for All Context Types
- **Auto-detect contexts for component diagrams** - Component diagrams now generated for all detected contexts, not just "background"
- **Fixes WebSocket server visualization** - Handler components now appear in DSL for "server" contexts
- **Fixes PWA/Worker visualization** - Works for "worker", "serviceworker", and all context types
- **Backward compatible** - Chrome extensions with "background" context work identically

**Impact**: Before this fix, component diagrams were only generated for Chrome extension "background" contexts, making the visualization feature broken for all non-extension projects (WebSocket servers, PWAs, workers) despite v0.3.0 adding manifest-optional support.

**Example**: Lingua CMS WebSocket server now generates full component diagrams:
```dsl
server = container "Server" {
  query_handler = component "Query Handler" { ... }
  command_handler = component "Command Handler" { ... }
  subscribe_handler = component "Subscribe Handler" { ... }
  unsubscribe_handler = component "Unsubscribe Handler" { ... }
}

component extension.server "Components_Server" {
  include *
  autoLayout tb
}
```

Fixes #7

## [0.3.6] - 2025-12-14

### Fixed

#### Bug Fixes Found by Test Suite
- **Correct ts-morph API usage** - Fixed `Node.isTypePredicate()` call (was incorrectly using `Node.isTypePredicateNode()`)
- **Prevent duplicate handler detection** - Skip else-if statements when processing if statements (they're already handled by the chain walker)

### Added

#### Comprehensive Test Suite
- **7 automated tests** covering all type guard detection patterns
- Tests for local type guards, imported guards, .ts extensions, path aliases, else-if chains
- Prevents regressions like the v0.3.2-v0.3.5 cycle

This version actually works correctly. v0.3.5 had the right approach (AST-based detection) but had implementation bugs that were caught and fixed by the new test suite.

## [0.3.5] - 2025-12-14

### Deprecated

Had bugs in implementation (wrong API method, duplicate detection). Use v0.3.6 instead.

### Fixed

#### Use AST-Based Type Predicate Detection (The Actual Fix)
- **Check AST structure, not resolved types** - Use `getReturnTypeNode()` and `Node.isTypePredicateNode()` instead of `getReturnType().getText()`
- **Fixes imported type guard detection** - ts-morph returns `"boolean"` for type predicates when checking resolved types across files, but AST structure preserves the actual type predicate
- **Works for all import patterns** - Path aliases, relative imports, with or without `.ts` extensions

### The Real Problem

When resolving imported functions, ts-morph's type system simplifies type predicates to their structural equivalent:
```typescript
// Function signature:
function isQuery(msg: Request): msg is Query { ... }

// What we were checking (WRONG):
def.getReturnType().getText()  // Returns "boolean" ❌

// What we now check (CORRECT):
def.getReturnTypeNode()  // Returns TypePredicateNode ✅
Node.isTypePredicateNode(returnTypeNode)  // true ✅
```

### What Changed

Both `findTypePredicateFunctions()` (local) and `resolveImportedTypeGuard()` (imported) now use AST-based detection:

```typescript
const returnTypeNode = node.getReturnTypeNode()

if (returnTypeNode && Node.isTypePredicateNode(returnTypeNode)) {
  const typeNode = returnTypeNode.getTypeNode()
  const typeName = typeNode.getText()  // "QueryMessage" ✅
  const messageType = extractMessageTypeFromTypeName(typeName)  // "query"
}
```

This works because AST nodes preserve the actual syntax structure, while resolved types represent semantic equivalence.

Fixes #6

## [0.3.4] - 2025-12-14

### Deprecated

Attempted to fix with compiler options. The actual issue was checking resolved types instead of AST structure. Use v0.3.5 instead.

## [0.3.3] - 2025-12-14

### Deprecated

This version implemented a manual fallback for import resolution. Use v0.3.5 instead.

## [0.3.2] - 2025-12-13

### Added

#### Imported Type Guard Detection
- **Cross-file resolution** - Automatically follows imports using ts-morph symbol resolution
- **Path alias support** - Works with tsconfig path aliases (@ws/, @/, etc.)
- **Named imports** - Detects type guards from `import { isQuery } from './messages'`
- **Relative imports** - Handles `./` and `../` imports correctly
- **Performance optimized** - Local lookup first, import resolution as fallback
- **Graceful error handling** - Skips resolution failures silently

### Example Enhancement
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

### Benefits
- No manual import parsing required - ts-morph handles complexity
- Works with all import patterns automatically
- Backward compatible - existing code works identically
- Enables full handler detection for projects like Lingua CMS

Addresses #4

## [0.3.1] - 2025-12-13

### Added

#### TypeScript Type Guard Pattern Detection
- **Type predicate detection** - Automatically detects TypeScript type guard functions (`msg is QueryMessage`)
- **If/else-if chain support** - Handles message routing with if/else-if chains using type guards
- **Message type extraction** - Extracts message types from type names (e.g., `QueryMessage` → `query`)
- **Fallback analysis** - Analyzes function body when type name doesn't match pattern (`return msg.type === 'query'`)
- **Performance optimized** - WeakMap caching prevents redundant file scanning (O(n) instead of O(n²))
- **Works alongside existing patterns** - Compatible with switch/case, handler maps, and `.on()` detection

### Example Pattern Detected
```typescript
function isQueryMessage(msg: RequestMessage): msg is QueryMessage {
  return msg.type === 'query'
}

if (isQueryMessage(message)) {
  response = await handleQuery(message)
} else if (isCommandMessage(message)) {
  response = await handleCommand(message)
}
```

### Benefits
- Detects handlers in TypeScript projects using type guard patterns
- Common in well-typed codebases for type narrowing and IDE support
- Enables full handler detection for projects like Lingua CMS

### Limitations
- Only detects type guards defined in the same file (imported type guards require enhancement)
- Future versions may add cross-file type guard resolution

Addresses #2

## [0.3.0] - 2025-12-12

### Added

#### Phase 1: Manifest-Optional Architecture Visualization
- **Make manifest.json optional** - Polly Visualize now works without manifest.json for WebSocket servers, generic TypeScript projects, PWAs, and Electron apps
- **Auto-detect project type** from manifest.json, package.json, or tsconfig.json
- **Simple context naming** - Use "server/client" instead of "websocket-server/websocket-client"
- **Improved CLI messaging** - Shows detected project type (Chrome Extension vs auto-detect)
- **Updated help text** - Lists all supported project types

#### Phase 2: Enhanced WebSocket Detection
- **Content analysis** - Analyzes server files to detect frameworks without relying solely on package.json
- **Framework-specific detection** for Bun, Node ws, Socket.io, Elysia, Express, Fastify, Hono, Koa
- **Confidence scoring system** with 15+ regex patterns to find the best server entry point
- **Distinguish server types** - Automatically labels as "WebSocket Server" vs "HTTP Server"
- **Bun built-in WebSocket support** - Works even without dependencies in package.json

#### Phase 3: Generic Message Pattern Detection
- **Extended handler detection** - Supports 5 new handler patterns beyond `.on()`:
  - `addEventListener('message', handler)` for Web Workers
  - `switch(message.type) { case 'EVENT': ... }` router patterns
  - `const handlers = { 'EVENT': fn }` handler map patterns
  - `ws.on('event', handler)` WebSocket handlers
  - `socket.on('event', handler)` Socket.io handlers

- **Extended flow detection** - Supports 5 new sender patterns beyond `.send()`:
  - `ws.send(message)` WebSocket messages
  - `socket.emit('event', data)` Socket.io events
  - `postMessage(data)` Web Worker/Window messages
  - `window.postMessage(data)` cross-window communication
  - `client.send()` broadcast patterns

### Changed
- ManifestParser constructor now accepts optional parameter for graceful handling of missing manifest
- ArchitectureAnalyzer automatically uses project detector when manifest is missing
- findProjectRoot() in visualize CLI checks for manifest.json OR package.json OR tsconfig.json

### Testing
- Added 11 unit tests for ManifestParser with optional manifest handling
- Integration tested with Chrome extension examples (backward compatible)
- Integration tested with WebSocket servers (Node ws, Bun)
- Tested comprehensive message pattern detection (10 handlers detected across all patterns)

### Migration Guide
No breaking changes! This release is 100% backward compatible:
- Chrome extensions with manifest.json work identically
- No API changes required
- Existing visualizations generate the same output

To use new features:
1. Run `polly visualize` in WebSocket/generic projects without manifest.json
2. Message patterns are detected automatically (no config needed)
3. Server framework detection works out of the box

## [0.2.1] - 2025-11-11

### Fixed
- **Verification Tool**: Fixed MessageRouter.tla not being found during Docker verification
  - CLI now searches multiple locations for MessageRouter.tla template file
  - Added support for external polly directory installations (git submodules, monorepos)
  - Bundled MessageRouter.tla specs with the published package
  - Improved error messaging when MessageRouter.tla cannot be found

## [0.2.0] - Previous release

(Previous changelog entries would go here)
