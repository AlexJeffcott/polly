# Changelog

All notable changes to @fairfox/polly-verify will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2025-12-15

### Added

- **Automatic project detection** - Polly now automatically detects your project type:
  - Chrome Extensions (via manifest.json)
  - WebSocket Servers (via ws, socket.io, elysia dependencies)
  - Progressive Web Apps (via service worker manifest)
  - Electron Apps (via electron dependency)
  - Generic TypeScript projects (fallback)

- **Architecture-specific TLA+ templates** - Built-in formal models with invariants:
  - `WebSocketServer.tla` - Hub-and-spoke pattern with:
    - ServerAlwaysAvailable invariant
    - ClientsRouteToServer invariant
    - NoClientToClientMessages invariant
  - `ChromeExtension.tla` - Multi-context extension pattern with:
    - BackgroundIsSingleton invariant
    - ContentScriptsAreTabScoped invariant
    - TabIsolation invariant
  - `GenericMessagePassing.tla` - Generic message systems with:
    - NoMessageLoss invariant
    - MessageOrdering invariant
    - NoDeadlock invariant

- **Project-specific configuration generation** - Config generator now produces project-type-specific settings:
  - WebSocket: `maxClients`, `maxMessagesPerClient`
  - Chrome Extension: `maxTabs`
  - PWA: `maxWorkers`, `maxClients`
  - Electron: `maxRenderers`
  - Generic: `maxContexts`

- **Template file management** - CLI automatically copies architecture-specific templates to generated specs directory

- **Range operator** - Added helper operator to all templates for sequence-to-set conversion

### Fixed

- **TLA+ generation bugs**:
  - Fixed IF/ELSE logic for single message type (was missing ELSE clause)
  - Fixed constant name mismatch (MaxMessages → MaxInFlight)
  - Fixed context name quoting in generated specs
  - Added MaxTabId for all project types (required by MessageRouter, set to 0 for non-Chrome projects)

- **Template integration**:
  - Template filenames now match module names (websocket-server.tla → WebSocketServer.tla)
  - INSTANCE statements now properly substitute template constants
  - Templates can now reference Range operator from parent modules

### Changed

- **API modernization** - Replaced manual adapter selection with `defineVerification`:
  ```typescript
  // Before (0.1.0)
  import { WebSocketAdapter } from '@fairfox/polly-verify'
  const adapter = new WebSocketAdapter({ ... })
  export default { adapter, state, ... }

  // After (0.2.0)
  import { defineVerification } from '@fairfox/polly-verify'
  export default defineVerification({ messages, state, ... })
  ```

- **CLI improvements**:
  - Better error messages with actionable suggestions
  - Clearer project detection feedback
  - Improved tsconfig.json missing file error

### Documentation

- **Complete README overhaul** - Updated to reflect automatic project detection and new API
- **WebSocket example documentation** - Updated example to show modern verification workflow
- **Architecture-specific examples** - Added examples for WebSocket, Chrome Extension, and PWA configurations

### Internal

- **Test coverage** - All 13 TLA generation tests passing, including template integration tests
- **Template validation** - Verified templates work end-to-end with Docker TLC verification

## [0.1.0] - Initial Release

### Added

- Initial implementation with manual adapter selection
- Chrome Extension verification support
- Basic TLA+ generation
- CLI tool for setup and verification

[0.2.0]: https://github.com/AlexJeffcott/polly/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/AlexJeffcott/polly/releases/tag/v0.1.0
