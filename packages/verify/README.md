# @fairfox/polly-verify

Formal verification for **any message-passing system** using TLA+.

## Overview

Polly Verify automatically detects your project type, generates TLA+ specifications from your TypeScript code, and verifies correctness properties about your application's message routing and state management.

**Works with:**
- ✅ Chrome Extensions (background, content, popup contexts)
- ✅ WebSocket Servers (hub-and-spoke architecture)
- ✅ Progressive Web Apps (service workers + clients)
- ✅ Electron Apps (main + renderer processes)
- ✅ Generic TypeScript (event buses, actor systems, custom patterns)

## Features

- **Automatic project detection** - Detects Chrome extensions, WebSocket servers, PWAs, Electron apps
- **Type-driven verification** - Extracts types from TypeScript, generates TLA+ automatically
- **Architecture-specific templates** - Built-in invariants for common patterns (hub-and-spoke, multi-context, etc.)
- **Interactive CLI** - Guided setup with smart configuration generation
- **Docker-based TLC** - No manual TLA+ toolchain setup required
- **Actionable errors** - Clear error messages with concrete suggestions

## Installation

```bash
# Using Bun (recommended)
bun add -D @fairfox/polly-verify

# Using npm
npm install --save-dev @fairfox/polly-verify

# Using pnpm
pnpm add -D @fairfox/polly-verify

# Using yarn
yarn add -D @fairfox/polly-verify
```

> **Note:** This is a development tool. Install as a dev dependency (`-D` flag).

## Quick Start

### 1. Generate Configuration

```bash
bunx polly verify --setup
```

Polly will:
- 🔍 Auto-detect your project type (WebSocket, Chrome extension, PWA, etc.)
- 📊 Analyze your TypeScript code for message handlers and state types
- 📝 Generate a verification configuration file

### 2. Review Configuration

Edit the generated `specs/verification.config.ts`:

```typescript
import { defineVerification } from "@fairfox/polly-verify"

export default defineVerification({
  messages: {
    maxInFlight: 2,       // Max concurrent messages
    maxClients: 2,        // WebSocket-specific: max concurrent clients
  },

  state: {
    // Define bounds for your state fields
    "connections.count": { min: 0, max: 100 },
    "users.online": { min: 0, max: 100 },
    "todos.count": { min: 0, max: 50 },

    // Booleans and enums are auto-configured
    "system.initialized": { type: "enum", values: ["false", "true"] },
  },

  // Optional: custom invariants
  invariants: [
    {
      name: "ConnectionsWithinLimit",
      expression: "state.connections.count <= state.connections.maxConcurrent",
      description: "Connection count must not exceed maximum",
    },
  ],

  onBuild: "warn",
  onRelease: "error",
})
```

### 3. Run Verification

```bash
bunx polly verify
```

Polly will:
- ✅ Generate TLA+ specifications
- ✅ Copy architecture-specific templates (WebSocketServer, ChromeExtension, etc.)
- ✅ Run TLC model checker via Docker
- ✅ Report any violations with counterexamples

## Project Type Detection

Polly automatically detects your project type:

| Project Type | Detection Method |
|-------------|------------------|
| **Chrome Extension** | Looks for `manifest.json` in root or `public/` |
| **WebSocket Server** | Detects `ws`, `socket.io`, or `elysia` dependencies |
| **PWA** | Looks for `public/manifest.json` with `service_worker` |
| **Electron** | Detects `electron` dependency |
| **Generic** | Falls back to generic message-passing model |

Once detected, Polly:
- Selects appropriate TLA+ templates
- Configures project-specific constants (maxClients, maxTabs, etc.)
- Infers message handler contexts correctly

## Examples

### WebSocket Server

```typescript
// specs/verification.config.ts
import { defineVerification } from "@fairfox/polly-verify"

export default defineVerification({
  messages: {
    maxInFlight: 2,
    maxClients: 3,              // WebSocket-specific
    maxMessagesPerClient: 2,
  },

  state: {
    "connections.count": { min: 0, max: 100 },
    "users.online": { min: 0, max: 100 },
  },

  onBuild: "warn",
  onRelease: "error",
})
```

### Chrome Extension

```typescript
// specs/verification.config.ts
import { defineVerification } from "@fairfox/polly-verify"

export default defineVerification({
  messages: {
    maxInFlight: 6,
    maxTabs: 2,                 // Extension-specific
  },

  state: {
    "user.role": { type: "enum", values: ["admin", "user", "guest"] },
    "todos": { maxLength: 10 },
  },

  onBuild: "warn",
  onRelease: "error",
})
```

### Progressive Web App

```typescript
// specs/verification.config.ts
import { defineVerification } from "@fairfox/polly-verify"

export default defineVerification({
  messages: {
    maxInFlight: 5,
    maxWorkers: 1,              // PWA-specific
    maxClients: 3,
  },

  state: {
    "cache.size": { min: 0, max: 50 },
    "sync.pending": { type: "boolean" },
  },

  onBuild: "warn",
  onRelease: "error",
})
```

## State Configuration

### Supported Types

**Boolean** - Auto-configured
```typescript
initialized: boolean
// → { type: 'enum', values: ["false", "true"] }
```

**Enum** - Auto-configured from union types
```typescript
role: "admin" | "user" | "guest"
// → { type: "enum", values: ["admin", "user", "guest"] }
```

**Number** - Requires bounds
```typescript
counter: number
// → { min: 0, max: 100 }
```

**Array** - Requires maximum length
```typescript
todos: Todo[]
// → { maxLength: 10 }
```

**String** - Requires concrete values or abstract flag
```typescript
userId: string
// → { values: ["user1", "user2", "guest"] }
// OR
// → { abstract: true }
```

**Map/Set** - Requires maximum size
```typescript
cache: Map<string, Data>
// → { maxSize: 5 }
```

## Custom Invariants

Define application-specific invariants:

```typescript
export default defineVerification({
  // ... messages, state ...

  invariants: [
    {
      name: "TodosWithinLimit",
      expression: "state.todos.count <= state.todos.maxTodos",
      description: "Todo count must not exceed maximum",
    },
    {
      name: "OnlineUsersValid",
      expression: "state.users.online <= state.users.total",
      description: "Online users cannot exceed total users",
    },
  ],
})
```

Invariants are checked at every state during model checking.

## CLI Commands

```bash
# Generate configuration (interactive setup)
bunx polly verify --setup

# Validate configuration (check bounds, detect issues)
bunx polly verify --validate

# Run verification (generate TLA+, run TLC)
bunx polly verify

# Show help
bunx polly verify --help
```

## Architecture

```
TypeScript Code
      ↓
[Project Detector] ──→ Detect: WebSocket / Chrome / PWA / Electron / Generic
      ↓
[Code Analyzer] ──────→ Extract: handlers, message types, state types
      ↓
[Config Generator] ───→ Generate: specs/verification.config.ts
      ↓
User fills in bounds ←─┘
      ↓
[TLA+ Generator] ─────→ Generate: UserApp.tla, MessageRouter.tla, templates
      ↓
[TLC (Docker)] ───────→ Model check with architecture-specific invariants
      ↓
Verification Results
```

### Architecture-Specific Templates

Polly includes TLA+ templates with invariants for common patterns:

**WebSocketServer.tla** - Hub-and-spoke pattern
- ServerAlwaysAvailable
- ClientsRouteToServer
- NoClientToClientMessages

**ChromeExtension.tla** - Multi-context extension pattern
- BackgroundIsSingleton
- ContentScriptsAreTabScoped
- TabIsolation

**GenericMessagePassing.tla** - Generic message systems
- NoMessageLoss
- MessageOrdering
- NoDeadlock

## Configuration Validation

The validator detects common issues:

- **Incomplete configuration** - `/* CONFIGURE */` markers not replaced
- **Null placeholders** - `null` values that need concrete values
- **Invalid bounds** - min > max, negative lengths, etc.
- **Unrealistic bounds** - Values that will slow verification significantly

Run `bunx polly verify --validate` to check your configuration.

## Development Workflow

### During Development

```typescript
export default defineVerification({
  // ... config ...
  onBuild: "warn",      // Show warnings, don't block builds
  onRelease: "error",   // Block releases on violations
})
```

- Verification runs on demand
- Violations are reported but don't block development
- Fast verification with small bounds

### Before Release

```bash
# Run full verification with realistic bounds
bunx polly verify
```

- Increase bounds in config for thorough checking
- Violations block the release
- Ensures shipped code is verified

## Docker Requirements

TLC runs inside Docker. Ensure Docker is installed and running:

```bash
# Check Docker is available
docker --version

# Polly will automatically pull the TLA+ image on first run
```

## Troubleshooting

### "Configuration file does not exist"

Run `bunx polly verify --setup` to generate the configuration.

### "Could not detect project structure"

Polly looks for:
- `manifest.json` (Chrome extensions)
- WebSocket dependencies in `package.json`
- `tsconfig.json` in project root

Ensure these files exist in expected locations.

### Verification is slow

Reduce bounds in your config:
- Lower `maxInFlight` (start with 2-3)
- Lower `maxClients`/`maxTabs` (start with 2)
- Reduce state field bounds

### TLC errors

Check the detailed log:
```
specs/tla/generated/tlc-output.log
```

## Examples

See [`examples/`](./examples/) for complete working examples:
- `websocket-app/` - WebSocket chat server with todos
- `chrome-extension/` - Browser extension example

## Contributing

This is part of the @fairfox/polly monorepo. See the main README for contribution guidelines.

## License

MIT
