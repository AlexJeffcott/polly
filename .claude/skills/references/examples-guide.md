# Examples Guide

Each example lives at `https://github.com/AlexJeffcott/polly/tree/main/examples/<name>`.

Docs live at `https://github.com/AlexJeffcott/polly/tree/main/docs`.

## Feature Matrix

| Feature | minimal | todo-list | full-featured | elysia-todo-app | webrtc-p2p-chat | team-task-manager |
|---------|---------|-----------|---------------|-----------------|-----------------|-------------------|
| `requires()`/`ensures()` | Yes | Yes | Yes | Yes | Yes | Yes |
| `$constraints()` | Yes | - | Yes | - | - | Yes |
| `stateConstraint()` | - | - | Yes | - | - | - |
| `$resource` | - | - | - | Yes | - | - |
| `{ verify: true }` | - | - | Yes | Yes | Yes | Yes |
| `{ type: "boolean" }` | Yes | Yes | Yes | Yes | - | - |
| `{ type: "number" }` | - | Yes | Yes | Yes | Yes | Yes |
| `{ type: "enum" }` | - | Yes | - | Yes | - | - |
| `perMessageBounds` | - | Yes | Yes | - | - | - |
| `temporalConstraints` | - | Yes | Yes | - | Yes | - |
| Parameter tracing | - | Yes | - | - | Yes | Yes |
| `tabSymmetry` | - | Yes | - | - | - | - |
| `hasLength()` | - | Yes | - | - | - | - |

## When to Reference Each Example

**"How do I get started?"** → `minimal/`
- Simplest background script with `$sharedState`, `requires()`, `ensures()`
- Basic verification config with `defineVerification()`

**"How do I set up full verification?"** → `todo-list/`
- Flagship example exercising every verification feature
- `{ type: "number" }` for maxTodos, priority enum, parameter tracing
- `perMessageBounds`, `temporalConstraints`, `tabSymmetry`
- Key files: `verification/verify.config.ts`, `src/background/handlers.ts`

**"Show me a complete Chrome extension"** → `full-featured/`
- All constraint styles combined: `requires()`/`ensures()`, `$constraints()`, `stateConstraint()`, `{ verify: true }`
- `stateConstraint("BookmarksRequireLogin", ...)` pruning impossible state combinations
- Numeric `bookmarkCount` state with verification
- Tier 1 + Tier 2 optimizations in config
- Key files: `src/background/index.ts`, `specs/constraints.ts`, `specs/verification.config.ts`

**"How do I use Polly with a web server?"** or **"How do I use $resource?"** → `elysia-todo-app/`
- Full-stack Elysia + Bun app with `$serverState`
- `$resource` for client-side async data fetching (`client/src/todosResource.ts`)
- Verified state for auth and todoCount, plus auto-generated `todos_status`/`todos_error` from `$resource`
- Real `defineVerification()` config for server-side
- Key files: `server/src/state.ts`, `server/src/handlers.ts`, `server/specs/verification.config.ts`, `client/src/todosResource.ts`

**"How do I verify real-time/P2P state?"** → `webrtc-p2p-chat/`
- Verified `peerCount` with `{ type: "number" }`
- Temporal constraints for join/leave ordering
- Parameter tracing on `isOnline` boolean
- Key files: `client/src/handlers.ts`, `client/specs/verification.config.ts`

**"How do I use $constraints() for role-based access?"** → `team-task-manager/`
- `$constraints()` for workspace-gated operations
- Role-based authorization patterns
- Verified `urgentTaskCount` with `{ type: "number" }`
- Key files: `client/src/handlers.ts`, `client/specs/constraints.ts`, `client/specs/verification.config.ts`

## Key Documentation Files

| Doc | URL Path | Covers |
|-----|----------|--------|
| Root README | `README.md` | Overview, quick start, all examples listed |
| State Guide | `docs/STATE.md` | Complete state primitives API, patterns, conflict resolution |
| Background Setup | `docs/BACKGROUND_SETUP.md` | `createBackground()` vs `getMessageBus()`, why it matters |
| Verify Specs | `tools/verify/specs/README.md` | TLA+ specifications, Docker setup for TLC |
