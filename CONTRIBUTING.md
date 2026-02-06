# Contributing to Polly

Thank you for your interest in contributing to Polly! This guide will help you get started.

Polly (πολύς - "many") is a multi-execution-context framework for building Chrome extensions, PWAs, and worker-based applications with reactive state and cross-context messaging.

## Getting Started

### Prerequisites

- [Bun](https://bun.sh/) 1.3.0 or later
- Chrome or Edge browser for testing Chrome extensions
- Git

### Setup Development Environment

1. **Clone the repository**:
   ```bash
   git clone <repository-url>
   cd polly
   ```

2. **Install dependencies and set up CLI**:
   ```bash
   bun run setup
   ```

   This command will:
   - Install all dependencies
   - Build the library with TypeScript declarations
   - Link the `polly` CLI globally

3. **Add CLI to your PATH** (add to `~/.zshrc` or `~/.bashrc`):
   ```bash
   export PATH="$HOME/.bun/bin:$PATH"
   ```

4. **Verify setup**:
   ```bash
   polly help
   ```

## Development Workflow

### Project Structure

```
polly/
├── src/                   # Main framework source
├── tools/
│   ├── verify/            # Formal verification tool
│   ├── visualize/         # Architecture visualization tool
│   └── analysis/          # Static analysis
├── examples/              # Example applications (Chrome extensions, web apps, etc.)
│   ├── minimal/           # Simplest starting point
│   ├── todo-list/         # CRUD with formal verification
│   ├── full-featured/     # Complete Chrome extension showcase
│   ├── elysia-todo-app/   # Full-stack web app (Elysia + Bun)
│   ├── webrtc-p2p-chat/   # P2P chat with WebRTC
│   └── team-task-manager/ # Collaborative task management
├── docs/                  # Documentation
└── specs/                 # TLA+ specifications
```

### Making Changes

1. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**

3. **Run quality checks**:
   ```bash
   bun run check
   ```

   This runs:
   - TypeScript type checking
   - Biome linter
   - Unit tests
   - Build verification

4. **Test your changes**:
   ```bash
   # Run all tests
   bun run test

   # Run specific test suites
   bun run test:framework        # E2E tests
   bun run test:watch            # Watch mode
   ```

5. **Format and lint**:
   ```bash
   bun run format                # Format code
   bun run lint                  # Check linting
   bun run lint:fix              # Auto-fix lint issues
   ```

### Testing

#### Unit Tests

```bash
bun run test
```

Unit tests are located alongside source files with `.test.ts` suffix.

#### E2E Tests

```bash
bun run test:framework           # Run all E2E tests
bun run test:framework:ui        # Run with Playwright UI
bun run test:framework:headed    # Run in headed mode
bun run test:framework:debug     # Run with debugging
```

E2E tests use Playwright to test real Chrome extension behavior.

#### Writing Tests

```typescript
// Unit test example
import { describe, test, expect } from "bun:test";

describe("MessageBus", () => {
  test("sends messages", async () => {
    const bus = getMessageBus("popup");
    const result = await bus.send({ type: "PING" });
    expect(result).toBeDefined();
  });
});

// E2E test example
import { test, expect } from "@playwright/test";

test("state syncs between contexts", async ({ page, context }) => {
  // Test implementation
});
```

### Building

```bash
# Build framework
bun run build

# Build library for publishing
bun run build:lib

# Production build
bun run build:prod
```

### Running Examples

Test your changes with the example extensions:

```bash
cd examples/full-featured
bun install
bun run build
```

Then load `dist/` in Chrome.

## Code Style

### TypeScript

- Use strict TypeScript settings
- Prefer type inference over explicit types
- Use `interface` for public APIs, `type` for internal
- **Never use type casting (`as`)** - use type guards instead

```typescript
// ❌ Bad - using type casting
const value = stored.settings as Settings;

// ✅ Good - using type guard
function isSettings(value: unknown): value is Settings {
  return value !== null && typeof value === "object" && "theme" in value;
}

if (isSettings(stored.settings)) {
  settings.value = stored.settings;
}
```

### Formatting

- Use Biome for formatting (configured in `biome.json`)
- 2-space indentation
- No semicolons (except where required)
- Single quotes for strings

### Naming Conventions

- **Files**: kebab-case (`message-bus.ts`)
- **Classes**: PascalCase (`MessageRouter`)
- **Functions**: camelCase (`getMessageBus`)
- **Constants**: UPPER_SNAKE_CASE (`DEFAULT_TIMEOUT`)
- **Types/Interfaces**: PascalCase (`ExtensionMessage`)

### Comments

- Use JSDoc for public APIs
- Explain **why**, not what
- Keep comments up to date

```typescript
/**
 * Creates a message bus for the specified context.
 *
 * @param context - The extension context (popup, background, etc.)
 * @returns A typed message bus instance
 */
export function getMessageBus<T>(context: string): MessageBus<T> {
  // Implementation
}
```

## Commit Messages

Follow the [Conventional Commits](https://www.conventionalcommits.org/) specification:

```
type(scope): description

[optional body]

[optional footer]
```

### Types

- **feat**: New feature
- **fix**: Bug fix
- **docs**: Documentation changes
- **style**: Code style changes (formatting, etc.)
- **refactor**: Code refactoring
- **test**: Adding or updating tests
- **chore**: Maintenance tasks

### Examples

```
feat(state): add $persistedState primitive

Add a new state primitive that persists to storage without syncing.
Useful for local-only state that should survive reloads.

Closes #123
```

```
fix(message-bus): prevent duplicate message handlers

MessageRouter now tracks registered handlers to prevent duplicates
when the background script is executed multiple times.
```

## Pull Requests

### Before Submitting

1. **Run all checks**:
   ```bash
   bun run check
   ```

2. **Test your changes**:
   ```bash
   bun run test
   bun run test:framework
   ```

3. **Update documentation** if needed

4. **Add tests** for new features

### PR Guidelines

- **Title**: Use conventional commit format
- **Description**: Explain what, why, and how
- **Link issues**: Reference related issues
- **Screenshots**: Add for UI changes
- **Breaking changes**: Clearly document

### PR Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
- [ ] Unit tests pass
- [ ] E2E tests pass
- [ ] Manual testing completed

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Comments added for complex code
- [ ] Documentation updated
- [ ] No breaking changes (or documented)
```

## Architecture Decisions

### State Management

- Use Preact signals for reactivity
- Lamport clocks for distributed consistency
- Chrome storage for persistence
- Ports for cross-context communication

### Type Safety

- No `any` types
- No type casting (`as`) - use type guards
- Strict TypeScript configuration
- End-to-end type safety

### Framework Philosophy

1. **Zero Magic**: Explicit, predictable behavior
2. **Type Safety First**: Compile-time guarantees
3. **Developer Experience**: Fast builds, great errors
4. **Framework Over Library**: Opinionated patterns
5. **Formal Correctness**: TLA+ for critical components

## Verification

### TLA+ Specifications

Critical components have TLA+ specifications in `specs/`:

```bash
# Start TLA+ environment
bun run tla:up

# Run verification
bun run tla:check

# Stop environment
bun run tla:down
```

### Formal Verification Tool

```bash
cd examples/full-featured
bun run verify              # Run verification
bun run verify --setup      # Generate config
```

## Documentation

### Where to Document

- **README.md**: High-level overview, quick start
- **Code comments**: Complex logic, non-obvious behavior
- **JSDoc**: Public APIs
- **Examples**: Working code samples
- **CONTRIBUTING.md**: Development guidelines

### Documentation Standards

- Clear and concise
- Include code examples
- Keep up to date
- Test examples (ensure they work)

## Release Process

(For maintainers)

### Publishing Strategy

The project uses a **single-package publishing model**:
- Only `@fairfox/polly` is published to npm
- Internal packages (verify, visualize, analysis) are marked `private: true`
- All tools are bundled into the main CLI
- Users get the complete framework and toolchain with one install

### Release Steps

1. **Update version** in `packages/polly/package.json`
2. **Update CHANGELOG.md**
3. **Run full test suite**:
   ```bash
   bun run check
   bun run test:all
   ```
4. **Build for production**:
   ```bash
   cd packages/polly
   bun run build:lib
   ```
5. **Publish to npm**:
   ```bash
   npm publish --access public
   ```

This publishes the framework with:
- Core runtime (state, message-bus, adapters)
- CLI with all commands (polly init, build, verify, visualize, etc.)
- Bundled verification and visualization tools
- TypeScript definitions
- Multi-platform support (Chrome extensions, PWAs, workers)

## Getting Help

- **Issues**: [GitHub Issues](https://github.com/AlexJeffcott/polly/issues)
- **Discussions**: [GitHub Discussions](https://github.com/AlexJeffcott/polly/discussions)
- **Email**: [maintainer email]

## Code of Conduct

- Be respectful and inclusive
- Welcome newcomers
- Focus on what's best for the community
- Show empathy towards others

Thank you for contributing! 🎉
