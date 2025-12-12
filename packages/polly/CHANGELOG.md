# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
