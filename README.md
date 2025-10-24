# Polly

> πολύς (polys) - "many" in Greek

A modern, type-safe framework for building **multi-execution-context applications** with reactive state management and cross-context messaging.

Perfect for: Chrome extensions, PWAs, Node/Bun/Deno apps with workers, and any application with multiple execution contexts.

## Features

- 🎯 **Type-Safe Messaging** - End-to-end type safety across all execution contexts
- ⚡️ **Reactive State** - Preact signals-based state management with automatic persistence
- 🔄 **Cross-Context Communication** - Unified message bus for seamless communication
- 🌐 **Multi-Platform** - Chrome extensions, PWAs, web workers, service workers, Node.js workers
- 🛠️ **Developer Tools** - Built-in CLI with build, test, lint, verify, and visualize commands
- 📊 **Architecture Visualization** - Automatic C4 architecture diagrams using Structurizr
- ✅ **Formal Verification** - TLA+ specifications for critical components
- 🚀 **Fast Builds** - Powered by Bun for lightning-fast development

## Quick Start

### Install

```bash
npm install -g @fairfox/polly
```

Or use with npx:

```bash
npx @fairfox/polly init my-app
```

### Create a New Project

```bash
polly init my-app
cd my-app
bun install
bun run build
```

### For Chrome Extensions

1. Open `chrome://extensions`
2. Enable "Developer mode"
3. Click "Load unpacked"
4. Select the `dist/` folder

### For PWAs with Workers

```bash
polly init my-pwa --template=pwa
# Coming soon: Additional templates for different architectures
```

## CLI Commands

### Project Setup
- `polly init [name]` - Create a new project
- `polly build` - Build for development
- `polly build --prod` - Build for production (minified)

### Development
- `polly check` - Run all checks (typecheck, lint, test, build, verify, visualize)
- `polly typecheck` - Type check your code
- `polly lint` - Lint with Biome
- `polly lint --fix` - Auto-fix lint issues
- `polly format` - Format code with Biome
- `polly test` - Run tests with Bun

### Analysis & Documentation
- `polly verify` - Run formal verification
- `polly verify --setup` - Generate verification config
- `polly visualize` - Generate architecture DSL
- `polly visualize --export` - Export static site with diagrams
- `polly visualize --serve` - Serve diagrams in browser

## Project Structure

```
polly/
├── packages/
│   ├── web-ext/           # Main framework package (to be renamed)
│   ├── verify/            # Formal verification tool
│   ├── visualize/         # Architecture visualization
│   ├── analysis/          # Static analysis tools
│   ├── tests/             # Integration tests
│   └── examples/          # Example applications
│       ├── minimal/       # Minimal Chrome extension
│       ├── todo-list/     # Todo list with storage
│       └── full-featured/ # Full-featured Chrome extension
├── scripts/               # Build and setup scripts
└── specs/                 # TLA+ specifications
```

## Architecture

The framework is built around three core concepts:

### 1. Message Bus

Unified messaging system for communication between execution contexts:

```typescript
import { getMessageBus } from "@fairfox/polly/message-bus";

const bus = getMessageBus<MyMessages>("main");

// Send messages
const result = await bus.send({ type: "GET_DATA" });

// Handle messages (in coordinator context)
bus.on("GET_DATA", async () => {
  return { data: [...] };
});
```

### 2. Reactive State

Preact signals-based state management with automatic persistence:

```typescript
import { $sharedState } from "@fairfox/polly/state";

const settings = $sharedState("settings", {
  theme: "dark",
  notifications: true,
});

// State is automatically persisted and synced across contexts
settings.value = { ...settings.value, theme: "light" };
```

### 3. Message Router

Automatic message routing between contexts in the coordinator:

```typescript
import { MessageRouter } from "@fairfox/polly/message-router";

const bus = getMessageBus("coordinator");
new MessageRouter(bus); // Handles all routing automatically
```

## Use Cases

- **Chrome Extensions**: popup ↔ background ↔ content scripts
- **PWAs**: main thread ↔ service worker ↔ web workers
- **Node.js Apps**: main process ↔ worker threads
- **Bun/Deno Apps**: main runtime ↔ workers
- **Any multi-context application** with isolated execution environments

## Examples

### Chrome Extensions

**Minimal Example** - Basic extension with background and popup:
```bash
cd packages/examples/minimal
bun run build
```

**Todo List Example** - Persistent storage and reactive state:
```bash
cd packages/examples/todo-list
bun run build
```

**Full-Featured Example** - Complete extension with authentication, bookmarks, and settings:
```bash
cd packages/examples/full-featured
bun run build
```

### Other Platforms (Coming Soon)

- **PWA with Service Worker** - Offline-first progressive web app
- **Node.js Worker App** - CPU-intensive task processing
- **Real-time Collaboration** - Multi-worker concurrent editing

## Development

### Setup Development Environment

```bash
bun install
bun run setup
```

### Run Tests

```bash
bun run test              # Run all tests
bun run test:watch        # Watch mode
bun run test:framework    # Framework tests only
```

### Build

```bash
bun run build             # Build framework
bun run build:lib         # Build library for publishing
bun run build:prod        # Production build
```

### Quality Checks

```bash
bun run typecheck         # Type check
bun run lint              # Lint
bun run format            # Format
bun run check             # Run all checks
```

### Verification & Visualization

```bash
cd packages/examples/full-featured
bun run verify            # Run formal verification
bun run visualize         # Generate architecture diagrams
bun run visualize:serve   # View diagrams in browser
```

## Framework Design Principles

1. **Type Safety First** - Leverage TypeScript for compile-time guarantees
2. **Zero Magic** - Explicit, predictable behavior without hidden abstractions
3. **Developer Experience** - Fast builds, great error messages, comprehensive tooling
4. **Framework Over Library** - Opinionated patterns that work well together
5. **Formal Correctness** - Critical components verified with TLA+

## Publishing

The framework is published as a single package `@fairfox/polly` that includes:
- Core framework (state management, message bus, adapters)
- CLI with all commands (build, test, verify, visualize)
- Development tools and analysis
- Multi-platform support

Internal packages (verify, visualize, analysis) are private workspace packages bundled into the main CLI.

## Contributing

Contributions are welcome! See [CONTRIBUTING.md](./CONTRIBUTING.md) for detailed guidelines.

Quick checks:

1. All tests pass: `bun run test`
2. Code is formatted: `bun run format`
3. No lint errors: `bun run lint`
4. Types are correct: `bun run typecheck`

Or run everything at once:

```bash
bun run check
```

## Philosophy

Polly (πολύς - "many") is designed for applications with **multiple execution contexts**:

1. **Multi-Context First** - Built from the ground up for distributed execution
2. **Type Safety** - End-to-end type guarantees across context boundaries
3. **Zero Magic** - Explicit, predictable behavior without hidden abstractions
4. **Framework Over Library** - Opinionated patterns that work well together
5. **Formal Correctness** - Critical components verified with TLA+

## Documentation

- [Framework API Reference](./packages/web-ext/README.md)
- [Contributing Guide](./CONTRIBUTING.md)
- [Examples](./packages/examples/)

## License

MIT

## Author

Alex Jeffcott
