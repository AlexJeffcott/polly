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

2. **Install dependencies**:
   ```bash
   bun install
   ```

3. **Build the library and link the CLI**:
   ```bash
   bun run build:lib
   bun link
   ```

   `build:lib` produces the runtime + TypeScript declarations under `dist/`.
   `bun link` exposes the `polly` binary defined by `package.json#bin` to the
   shell. After the link step, add bun's bin dir to your `PATH` if you haven't
   already:

   ```bash
   export PATH="$HOME/.bun/bin:$PATH"
   ```

4. **Verify the install**:
   ```bash
   polly --help
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

#### Unit tests

```bash
bun run test                    # Runs the tests workspace via bun:test
bun run test:watch              # Same, with watch mode
```

Unit tests live in the `tests/` workspace, organised by area
(`tests/unit/quality/`, `tests/unit/state/`, etc.). The colocated
`*.test.ts` pattern is also used inside `tools/` (e.g.
`tools/verify/src/__tests__/`).

#### Browser tests

Tests for code that needs a real DOM (Preact rendering, WebRTC
adapters, etc.) run through a Puppeteer harness:

```bash
polly test:browser tests/browser           # Or any directory holding *.browser.ts
```

The harness is implemented in `tools/test/src/browser/`. Each
`*.browser.ts` file is bundled with `Bun.build`, served on an
ephemeral port, and its results collected back to the runner.

#### Example test suites

```bash
bun run test:examples           # Lint + typecheck + verify three examples
bun run test:tiers verify --only=visualize  # End-to-end test of `polly visualize`
bun run test:all                # Lint + typecheck + tests + examples + e2e
```

#### Writing tests

```typescript
import { describe, test, expect } from "bun:test";
import { createMockAdapters } from "@fairfox/polly/test";

describe("MessageBus", () => {
  test("sends messages", async () => {
    const adapters = createMockAdapters();
    // ... wire up the bus against the mock adapters, send a message,
    // assert against adapters.runtime._sentMessages.
  });
});
```

#### Test the factory entry points, not only hand-wired stacks

If the project ships a factory or composite entry point —
`createMeshClient`, `createPeerRepoServer`, any `createX` or
`configureX` helper — there must be a test that exercises that exact
entry point end-to-end. Hand-wired tests that bypass the factory are
useful as unit scaffolds; they are not a substitute.

0.27.0 of this package shipped a bug where `createMeshClient` omitted
the `peerId` option to `new Repo(...)`. Automerge auto-generated a
random id, `MeshNetworkAdapter` stamped every outgoing envelope with
that auto-id as its `senderId`, and the remote receiver — whose
`knownPeers` was keyed by the mesh peer id the application had paired
against — silently dropped every message at the signature step. The
full test suite passed, including the browser e2e harness, because
`tests/browser/mesh-webrtc.browser.ts` wired the stack by hand and
passed an explicit `peerId` to `new Repo(...)`. The test silently
compensated for the factory's gap. Every downstream consumer of the
factory — fairfox, any external application — saw real-world sync
break, with no signal from any tier of the suite that anything was
wrong.

`tests/browser/mesh-client-roundtrip.browser.ts` is the pattern to
mirror when adding a new factory: two clients built through the
public API with mutually-paired keyrings, a real WebRTC data channel,
a document round-trip. Run the test in two states before committing
it — green against your fix, red against the unfixed code — so you
know the test actually exercises the path it claims to.

A hand-wired test tells you the pieces work. A factory-path test
tells you the assembly ships correctly. You need both.

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

- Biome handles formatting; see `biome.json`.
- 2-space indentation.
- Double quotes for strings.
- Semicolons always.
- Trailing commas where ES5 permits them (objects, arrays).

Run `bun run format` before committing — or rely on biome via your
editor.

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

## Commit messages and PR descriptions

Commits and PR descriptions are written in plain English. They describe
the change and the reason for it, not its mechanics. They are written
from the task description (and any refinement notes), not from the
diff.

Avoid the Conventional-Commits prefix grammar (`feat:`, `fix:`, etc.) —
the project does not use it.

Avoid:

- Sentence-starter scope tags (`docs:`, `chore:`).
- Bulleted "What changed" lists that restate the diff.
- "Test steps" or "How to test" sections in PR bodies (CI proves the
  test plan ran; the PR body explains the change).
- Authorship attributions or co-author trailers added by tooling
  unless the user has explicitly asked for them on a given commit.

A good commit message reads like a short note from the author to a
future reader: what was done, what motivated it, and any constraint a
reader might need to know about the result.

## Pull Requests

### Before submitting

1. `bun run check` passes.
2. `bun run test` passes locally.
3. The relevant browser, example, or e2e suite passes if you touched
   code those exercise.
4. The change is documented where a reader would expect to find it
   (README, the matching `docs/*.md`, or the example's README).

### Guidelines

- The PR title is the same one-line summary you'd write in a commit.
  Plain English; no `feat:` / `fix:` prefix.
- The description is one or two paragraphs that explain the change and
  the reason for it. See "Commit messages and PR descriptions" above.
- Reference related issues with `Closes #N` or `Refs #N`.
- For UI changes, attach a screenshot or short clip.
- Breaking changes are called out explicitly in the description and
  in `CHANGELOG.md`.

## Architecture notes

State primitives are built on Preact signals. Cross-context
synchronisation uses Lamport clocks for ordering, Chrome storage (or
the equivalent web adapter) for persistence, and ports plus
`BroadcastChannel` for transport. The peer and mesh tiers replace the
storage layer with Automerge CRDT replicas and WebRTC data channels.

Type-safety rules are enforced by the conformance plugin under
`polly quality run`: no `any`, no `as` casts outside `as const` and the
explicit `as unknown as Y` escape hatch, no `require(...)`, no
`node:`/`bun:` imports inside browser-targeted code, no decorative
comment banners or marketing prose. The full list of rules is in
`tools/quality/src/plugins/`.

## Verification

Polly ships a TLA+/TLC pipeline as a first-class part of the
toolchain. From inside any example:

```bash
cd examples/todo-list
polly verify                # Lints, generates spec, runs TLC
polly verify --setup        # Scaffold a specs/verification.config.ts
```

The generator lives at `tools/verify/`. Handler-level `requires()` and
`ensures()` annotations are runtime no-ops; the verifier reads them
statically to build invariants and temporal properties.

For subsystem-scoped runs and the supporting handlers, see
`docs/TLA_RESOURCES.md` and the verification config shipped with the
todo-list example.

## Documentation

### Where to document

- `README.md` for the entry-point pitch and the smallest end-to-end
  example.
- `docs/*.md` for feature areas (state, messaging, adapters, testing,
  UI, CSS, actions, errors, logging, background setup, TLA+).
- JSDoc on every public export — these surface in editor tooltips and
  in generated declaration files.
- Example READMEs for runnable, copy-paste-ready usage.

Documentation is held to the same conformance bar as code: the
`polly:no-banners`, `polly:no-decorative-emoji`, `polly:no-marketing`,
`polly:no-note-prefix`, and `polly:no-commented-code` checks run over
`docs/` (and the marketing check covers prose), so the same rules that
keep source clean keep the documentation clean.

## Release process

(For maintainers.)

Polly publishes a single package, `@fairfox/polly`. The internal tool
packages (verify, visualize, analysis, quality, test) are bundled into
that one publish via subpath exports declared in `package.json`. Steps:

1. Bump `version` in `package.json` and add a `CHANGELOG.md` entry.
2. `bun run check && bun run test:all`.
3. `bun run build:lib`.
4. `npm publish --access public`.

## Getting help

- Issues: [GitHub Issues](https://github.com/AlexJeffcott/polly/issues)
- Discussions: [GitHub Discussions](https://github.com/AlexJeffcott/polly/discussions)
