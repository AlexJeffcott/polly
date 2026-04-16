---
name: polly
description: Expert guide for the @fairfox/polly framework covering state management, peer-first/mesh state (CRDTs, WebRTC, encryption), async resources, formal verification (TLA+), quality tooling, and best practices. Use when working with Polly state primitives ($sharedState, $syncedState, $state, $serverState, $peerState, $meshState), async data fetching ($resource), verification features (requires/ensures, $constraints, stateConstraint, defineVerification), quality checks (no-as-casting), browser test harness, or when auditing code to maximize Polly feature usage. Triggers on any work involving @fairfox/polly imports, peer-first/mesh state setup, Automerge CRDTs, WebRTC data channels, verification setup, TLA+ model checking, message handler contracts, $resource async patterns, or questions about Polly patterns and examples.
---

# Polly Expert (up to v0.21.0)

Maximize usage of the @fairfox/polly framework's state management, async resources, peer-first/mesh state, and formal verification features. This skill covers the Polly framework up to and including version 0.21.0.

## Quick Reference

**Imports** (use these exact paths):
```typescript
import { $sharedState, $syncedState, $state } from '@fairfox/polly/state'
import { $resource } from '@fairfox/polly'
import { requires, ensures, $constraints, stateConstraint, defineVerification } from '@fairfox/polly/verify'
import { createBackground } from '@fairfox/polly/background'
import { validateShape } from '@fairfox/polly'

// Peer-first state (v0.21.0)
import { $peerState, $peerText, $peerCounter, configurePeerState, createPeerStateClient } from '@fairfox/polly'
import { $meshState, $meshText, $meshCounter, configureMeshState, MeshNetworkAdapter, MeshWebRTCAdapter } from '@fairfox/polly'

// Quality tooling (v0.21.0)
import { checkNoAsCasting, isLineClean, suggestFix } from '@fairfox/polly/quality'

// Browser test harness (v0.21.0)
import { describe, test, expect, done, flush, cleanup } from '@fairfox/polly/test/browser'
```

## Workflow

### New Project Setup

1. Set up background with `createBackground()` (NEVER `getMessageBus('background')`)
2. Define state with `$sharedState` (add `{ verify: true }` for verified state)
3. Add `requires()`/`ensures()` to every message handler
4. Create `specs/verification.config.ts` with `defineVerification()`
5. Run `polly verify --estimate` to check feasibility
6. Run `polly verify` to generate and check TLA+

### Auditing Existing Code

Scan for these issues in order of impact:

1. **Missing `requires()`/`ensures()`** - Every handler with preconditions or postconditions should declare them
2. **`getMessageBus('background')`** - Replace with `createBackground()` to prevent double-execution
3. **`@fairfox/polly-verify`** imports - Replace with `@fairfox/polly/verify`
4. **`VerificationConfig` type** - Replace with `defineVerification()` call
5. **State without `{ verify: true }`** - Any state referenced in requires/ensures/constraints needs it
6. **Missing verification config** - Should exist at `specs/verification.config.ts`
7. **No `perMessageBounds`** - Add for realistic concurrency modeling
8. **No `temporalConstraints`** - Add when message ordering matters (login before logout, etc.)
9. **Numeric state as boolean** - Use `{ type: "number", min, max }` instead of boolean proxies
10. **Correlated fields without `stateConstraint()`** - If two fields are structurally dependent (e.g., bookmarks require login), use `stateConstraint()` to prune impossible states from TLC exploration
11. **Large handler set without `subsystems`** - If monolithic verification is infeasible (>15 handlers, >6 state subsystems), add `subsystems` to `defineVerification()` for compositional verification
12. **No `--estimate` before first run** - Run `polly verify --estimate` to check feasibility before committing to a full verification run
13. **Weak `ensures()` postconditions** - `ensures(x !== y)` when handler concretely assigns `x = z` should be `ensures(x === z)`
14. **No `verification.timeout`** - Add `verification: { timeout: 300 }` to prevent runaway TLC runs on large state spaces
15. **Async fetch with signal reads after `await`** - Replace with `$resource` to separate sync tracking from async work
16. **Manual loading/error state for fetches** - `$resource` provides `status` and `error` signals automatically

## Peer-First State (v0.21.0)

Polly offers three resilience tiers for state that needs to survive server loss or bypass the server entirely.

| Tier | Primitive | Server's role | Resilience |
|------|-----------|---------------|------------|
| Weakest | `$sharedState` | Source of truth | Server backups |
| Middle | `$peerState` | Full peer on the data path | Any device can rehydrate the server |
| Strongest | `$meshState` | Not on the data path | App works with zero server uptime |

### $peerState — Server as a peer

Every device holds a full Automerge CRDT replica. The server holds one too, so cron and HTTP handlers can read and mutate documents. If the server loses its storage, any reconnecting client repopulates it.

```typescript
import { createPeerStateClient, configurePeerState, $peerState } from '@fairfox/polly'

const client = createPeerStateClient({ url: 'wss://yourapp.com/polly/peer' })
configurePeerState(client.repo)

const settings = $peerState('settings', { theme: 'dark' })
await settings.loaded
settings.value = { theme: 'light' } // syncs to every peer
```

**Options:**
- `sign: true` on `createPeerStateClient` — enables Ed25519 signing via MeshNetworkAdapter in sign-only mode (no encryption). The server can still parse Automerge sync messages.

**Server setup:**
```typescript
import { createPeerRepoServer } from '@fairfox/polly'
// or as Elysia plugin:
import { peerRepo } from '@fairfox/polly/elysia'
```

### $meshState — No server on the data path

Peers exchange operations directly over WebRTC data channels, signed with Ed25519 and encrypted with XSalsa20-Poly1305. A small stateless signalling server helps peers find each other; removing it does not affect running connections.

```typescript
import { configureMeshState, $meshState, MeshNetworkAdapter, MeshWebRTCAdapter } from '@fairfox/polly'

const repo = new Repo({ network: [new MeshNetworkAdapter({ base: webrtcAdapter, keyring })] })
configureMeshState(repo)

const notes = $meshState('notes', { entries: [] })
```

**Key exchange:** First-time pairing uses `createPairingToken` / `applyPairingToken` (displayed as QR code). Compromised devices are revoked via `createRevocation` / `applyRevocation`.

**Signalling server:**
```typescript
import { signalingServer } from '@fairfox/polly/elysia'
```

### Choosing a resilience tier

| Need | Use |
|------|-----|
| Server is source of truth, simple setup | `$sharedState` |
| Server participates but clients can recover it | `$peerState` |
| Server never sees the data | `$meshState` |
| Mix in one app | Yes — public settings in `$sharedState`, collaborative docs in `$peerState`, private notes in `$meshState` |

See `docs/STATE.md` for the full decision tree and `docs/RFC-041-choosing.md` for design rationale.

### Specialised CRDT primitives

Each tier has specialised variants for common Automerge types:

| Primitive | What it does |
|-----------|-------------|
| `$peerText` / `$meshText` | Automerge text (updateText) |
| `$peerCounter` / `$meshCounter` | Automerge Counter (increment with delta) |
| `$peerList` / `$meshList` | Automerge list (array replacement) |

## Quality Tooling (v0.21.0)

### No-as-casting conformance check

Bans TypeScript `as` type assertions codebase-wide. Only `as const` and the explicit escape hatch `as unknown as` are allowed. Violations include pattern-specific fix advice.

```typescript
import { checkNoAsCasting } from '@fairfox/polly/quality'

const result = await checkNoAsCasting({ rootDir: process.cwd() })
if (result.violations.length > 0) {
  result.print()
  process.exit(1)
}
```

### Browser test harness

Puppeteer-based harness for testing browser-only code (WebRTC adapters, Preact components, anything needing real DOM). Bundles each test file with Bun.build, serves on an ephemeral port, and collects results.

```typescript
import { describe, test, expect, done, flush, cleanup } from '@fairfox/polly/test/browser'

describe('my component', () => {
  test('renders', async () => {
    render(<MyComponent />, app)
    await flush()
    expect(app.querySelector('h1')).toHaveTextContent('Hello')
    cleanup(app)
  })
})

done()
```

Run with `bun tools/test/src/browser/run.ts tests/browser`.

**Matchers:** toBe, toEqual, toContain, toBeTruthy, toBeFalsy, toBeNull, toBeDefined, toBeUndefined, toBeGreaterThan, toHaveLength, toExist, toHaveTextContent, toBeChecked, toBeDisabled, toHaveValue, toHaveAttribute. All support `.not`.

## Anti-Patterns

| Anti-Pattern | Correct Pattern |
|---|---|
| `getMessageBus('background')` | `createBackground()` |
| `import from '@fairfox/polly-verify'` | `import from '@fairfox/polly/verify'` |
| `const config: VerificationConfig = {...}` | `export default defineVerification({...})` |
| `if (!state.loggedIn) throw new Error(...)` | `requires(state.loggedIn === true, '...')` |
| `loggedIn: { type: "boolean" }` when field name mismatches | `loggedIn: [false, true]` |
| Signal reads inside `async` after `await` | `$resource` with `source`/`fetcher` split |
| Manual `isLoading`/`error` state for fetches | `$resource` `status`/`error` signals |

## $resource — Async Data Fetching

`$resource` separates synchronous dependency tracking (`source`) from async work (`fetcher`), solving the broken-tracking problem at `await` boundaries. Signal reads inside an `async` function are invisible after the first `await` — `$resource` avoids this by extracting dependencies synchronously.

```typescript
import { $resource } from '@fairfox/polly'

const todos = $resource<{ userId: number | null }, Todo[]>('todos', {
  source: () => ({ userId: user.value?.id ?? null }),  // Fully tracked
  fetcher: async ({ userId }) => {                      // No signal reads here
    if (userId === null) return []
    const res = await fetch(`/api/todos?userId=${userId}`)
    return res.json()
  },
  initialValue: [],
})

todos.data     // Signal<Todo[]>
todos.status   // Signal<"idle" | "loading" | "success" | "error">
todos.error    // Signal<Error | undefined>
todos.refetch()
```

**Rules:**
- `source()` is synchronous — all signal reads (`.value`) go here
- `fetcher()` is async — receives source output as parameter, must NOT read signals
- `initialValue` is returned before the first successful fetch
- `refetch()` re-runs the fetcher with current source values
- Deep equality check on source output prevents redundant fetches
- Stale responses are discarded (generation counter prevents race conditions)

### $resource + Verification

Each `$resource` auto-generates three synthetic handlers for TLA+ verification:

| Synthetic Handler | Precondition | Assignments |
|---|---|---|
| `{name}_FetchStart` | `status !== "loading"` | `status = "loading"`, `error = false` |
| `{name}_FetchSuccess` | `status === "loading"` | `status = "success"`, `error = false` |
| `{name}_FetchError` | `status === "loading"` | `status = "error"`, `error = true` |

Auto-generated state fields are added to verification config:
```typescript
state: {
  todos_status: { type: 'enum', values: ['idle', 'loading', 'success', 'error'] },
  todos_error: { type: 'boolean' },
}
```

These synthetic handlers are auto-discovered when the `$resource` file is in the analyzed tsconfig scope — no manual registration needed.

## Handler Pattern

```typescript
bus.on('MESSAGE_TYPE', async (payload) => {
  // 1. Preconditions
  requires(loginState.value.loggedIn === true, 'Must be logged in')

  // 2. Business logic
  const result = doWork(payload)
  state.value = newState

  // 3. Postconditions
  ensures(state.value === expected, 'State must be updated')

  return { success: true, result }
})
```

## stateConstraint() — Pruning Impossible States

`stateConstraint()` maps to the TLC `CONSTRAINT` clause. Unlike `invariant()` (which checks but still explores all states), `stateConstraint()` **discards** structurally impossible states from the exploration queue entirely, dramatically reducing state spaces for correlated fields.

```typescript
import { stateConstraint } from '@fairfox/polly/verify'

// "A leader must be connected" — prune states where isLeader=true but status!="connected"
stateConstraint("LeaderRequiresConnection", () =>
  !connectionState.value.isLeader || connectionState.value.status === "connected"
)

// With optional message
stateConstraint(
  "BookmarksRequireLogin",
  () => bookmarkCount.value <= 0 || loginState.value.loggedIn === true,
  { message: "Cannot have bookmarks without being logged in" },
)
```

**When to use:**
- Two or more state fields are structurally correlated (one field's value constrains another's)
- `requires()` guards only skip one action — they don't prune the underlying state
- `invariant()` flags violations but TLC still wastes time exploring those states

**How it works:**
1. Runtime: complete no-op (like `requires()`/`ensures()`)
2. Static analysis: the arrow function body is extracted as a string
3. TLA+ codegen: translated via `tsExpressionToTLA()` and added to `StateConstraint ==` as `/\ \A ctx \in Contexts : (<translated expression>)`

**Expression rules:** Same as requires/ensures — use `signalName.value.field` or `state.field` references, `===`, `!==`, `&&`, `||`, and negation.

## Verification Config Pattern

```typescript
// specs/verification.config.ts
import { defineVerification } from '@fairfox/polly/verify'

export default defineVerification({
  state: {
    loggedIn: [false, true],                          // boolean
    itemCount: { type: 'number', min: 0, max: 100 },  // numeric
    priority: { type: 'enum', values: ['low', 'med', 'high'] }, // enum
  },
  messages: {
    maxInFlight: 2,
    maxTabs: 1,
    include: ['MSG_A', 'MSG_B', 'MSG_C'],
    perMessageBounds: { 'MSG_A': 1, 'MSG_B': 2 },
  },
  tier2: {
    temporalConstraints: [
      { before: 'LOGIN', after: 'LOGOUT', description: 'Must login first' },
    ],
    boundedExploration: { maxDepth: 15 },
  },
  verification: {
    timeout: 300,   // seconds (0 = no limit, max 3600)
    workers: 4,     // TLC threads (1–16, default 1)
  },
  onBuild: 'warn',
  onRelease: 'error',
})
```

## Subsystem-Scoped Verification (Compositional)

When monolithic verification is infeasible (too many handlers/state fields), split into subsystems. Each subsystem is verified independently; non-interference guarantees compositional soundness.

```typescript
export default defineVerification({
  state: {
    'appState.appPhase': { type: 'enum', values: ['idle', 'initializing', 'ready', 'error'] },
    'authState.authPhase': { type: 'enum', values: ['idle', 'loading', 'authenticated', 'error'] },
    'connectionState.status': { type: 'enum', values: ['disconnected', 'connecting', 'connected'] },
  },

  subsystems: {
    appLifecycle: {
      state: ['appState.appPhase'],
      handlers: ['MarkAppInitializing', 'MarkAppInitialized', 'MarkAppError', 'ResetAppState'],
    },
    auth: {
      state: ['authState.authPhase'],
      handlers: ['StartAuthLoading', 'AuthSuccess', 'AuthError', 'Logout', 'ResetAuthState'],
    },
    connection: {
      state: ['connectionState.status'],
      handlers: ['StartConnecting', 'Connected', 'Disconnected', 'ResetConnectionState'],
    },
  },

  messages: { maxInFlight: 2, maxTabs: 1 },
  onBuild: 'warn',
  onRelease: 'error',
})
```

**Rules:**
- `state`: array of field names from the top-level `state` config — must be partitioned (no field in multiple subsystems)
- `handlers`: array of message type names — must be partitioned (error if a handler appears in multiple subsystems)
- Handlers not assigned to any subsystem are warned about and not verified
- Non-interference is checked automatically: no handler may write to state owned by another subsystem
- If `subsystems` is omitted, monolithic verification runs as before (backward compatible)

**Output:**
```
Subsystem verification results:
  ✓ appLifecycle    4 handlers  16 states   0.3s
  ✓ auth            5 handlers  12 states   0.2s
  ✓ connection      4 handlers  8 states    0.1s

  Non-interference: ✓ verified (no cross-subsystem state writes)

Compositional result: ✓ PASS
```

## State Space Estimator (`polly verify --estimate`)

Pre-flight estimation of state space size without running TLC or Docker. Helps users gauge verification feasibility before committing to a full run.

```bash
polly verify --estimate
```

**Example output:**
```
State space estimation:

  Fields analyzed:       5
  Field product:        120
  Handlers:             8
  Max in flight:        2
  Contexts (tabs + bg): 2

  Interleaving factor:  56
  Estimated states:     ~673920

  Assessment: slow (may take 10–30 minutes)

  Suggestions:
    • Consider splitting into subsystems
    • Consider reducing bounds for field "bookmarkCount" (21 values)
    • Reducing maxInFlight from 2 to 1 would reduce interleaving by ~8x
```

**Feasibility levels:** `trivial` | `feasible` | `slow` | `infeasible`

**When to suggest:** If a user's verification is slow or they're unsure about config tuning, recommend `--estimate` first.

## Compile-Time Expression Validation

Polly validates `requires()`/`ensures()` expressions before TLA+ codegen, catching patterns that would produce broken or weak TLA+. Warnings run automatically during `polly verify` and `polly verify --estimate`.

**Warning kinds:**

| Kind | Trigger | Suggestion |
|------|---------|------------|
| `unmodeled_field` | References field not in state config | Add field to config or remove from expression |
| `unsupported_method` | Calls `.some()`, `.filter()`, etc. | Rewrite as simple comparisons |
| `optional_chaining` | Uses `?.` which is fragile to translate | Use explicit null checks |
| `null_comparison` | Compares non-nullable field to null | Remove comparison |
| `weak_postcondition` | `ensures(x !== y)` when concrete assignment exists | Use `ensures(x === z)` for stronger postcondition |

**Example output:**
```
⚠️  Found 2 expression warning(s):

   ⚠  requires() in USER_LOGIN references unmodeled field 'profile'
      requires(state.profile.tier === "premium")
      at src/handlers.ts:42
      → Add 'profile' to state config or remove from requires()

   ⚠  ensures() in BOOKMARK_ADD uses !== for 'count' which has a concrete assignment
      ensures(state.count !== 0)
      at src/handlers.ts:89
      → Consider ensures(count === 1) for a stronger postcondition
```

**When auditing:** Flag `ensures()` calls using `!==` when a concrete value is assigned in the handler — a `===` postcondition is always stronger.

## Verification Engine Options

Optional timeout and worker thread config for TLC runs:

```typescript
export default defineVerification({
  state: { /* ... */ },
  messages: { maxInFlight: 2, maxTabs: 1 },

  verification: {
    timeout: 300,    // seconds (0 = no limit, max 3600)
    workers: 4,      // TLC worker threads (1–16, default 1)
  },
})
```

**When to suggest:** For large state spaces where `--estimate` reports `slow`, recommend adding `timeout` to prevent runaway verification and `workers` to parallelize TLC exploration.

## State Space Tuning Guide

TLA+ model checking explores every reachable state. The config knobs below control state space size — tune them to balance **realism** vs **verification speed**.

### `maxInFlight` (messages.maxInFlight)

How many messages can be processing simultaneously. This is the single most impactful setting.

| Value | Effect | Use when |
|-------|--------|----------|
| 1 | Sequential only — **misses all concurrency bugs** | Never in production configs; only for initial smoke tests |
| 2 | Pairwise interleaving — catches most real race conditions | **Default recommendation** |
| 3+ | Diminishing returns, exponential state explosion | Only if you have specific 3-way race conditions to verify |

**Rule**: Always use `maxInFlight: 2` unless verification is too slow, then add `temporalConstraints` to prune unrealistic interleavings rather than dropping to 1.

### `temporalConstraints` (tier2.temporalConstraints)

Prune unrealistic message orderings to reduce state space without losing realism. More surgical than reducing `maxInFlight`.

```typescript
temporalConstraints: [
  { before: 'authenticate', after: 'Logout', description: 'Must auth before logout' },
  { before: 'StartConnecting', after: 'Connected', description: 'Must start before connected' },
]
```

**When to add**: If `maxInFlight: 2` is too slow, add temporal constraints for obvious causal orderings before reducing maxInFlight. Each constraint significantly prunes the state graph.

### `maxTabs` (messages.maxTabs)

Number of tab contexts to model. Each additional tab multiplies state space.

| Value | Effect |
|-------|--------|
| 1 | Single-tab verification (sufficient for most apps) |
| 2 | Cross-tab coordination bugs (leader election, shared state) |
| 3+ | Rarely needed; extreme state explosion |

**Rule**: Use 1 unless your app has explicit cross-tab coordination (leader election, broadcast channels). If it does, use 2.

### `perMessageBounds` (messages.perMessageBounds)

Limits how many times each message type can appear in a trace. Prevents unbounded repetition.

```typescript
perMessageBounds: {
  authenticate: 1,    // Auth happens once per session
  query: 2,           // Might retry once
  ResetAppState: 1,   // Reset is rare
}
```

**Rule**: Set to 1 for one-shot operations (auth, init, reset). Set to 2-3 for operations that legitimately retry or repeat. Omit entries for messages with no natural bound (they fall back to the global limit).

### `maxDepth` (tier2.boundedExploration.maxDepth)

Maximum number of state transitions to explore in any single trace.

| Value | Effect |
|-------|--------|
| 5-8 | Fast but may miss deep bugs |
| 10-15 | Good balance for most apps |
| 20+ | Thorough but slow; use with tight `perMessageBounds` |

**Rule**: Start at 10. Increase if verification passes too quickly (under 5s) — you may not be exploring enough. Decrease if it's too slow, but prefer adding `temporalConstraints` first.

### `stateConstraint()` (code-level)

Prune structurally impossible states from exploration. More powerful than `temporalConstraints` for correlated fields because it eliminates entire regions of the state space.

```typescript
stateConstraint("BookmarksRequireLogin", () =>
  bookmarkCount.value <= 0 || loginState.value.loggedIn === true
)
```

**When to add**: If two fields are always correlated (e.g., "can't have bookmarks without being logged in"), adding a `stateConstraint()` prevents TLC from ever exploring those impossible combinations. This can reduce state space by orders of magnitude.

### Tuning workflow

1. Start with `maxInFlight: 2`, `maxDepth: 10`, `maxTabs: 1`
2. Run `polly verify --estimate` to check feasibility before a full run
3. Add `stateConstraint()` for any structurally correlated fields
4. Run verification. If too slow (>5 min), add `temporalConstraints` for obvious causal orderings
5. If still too slow, tighten `perMessageBounds` for rare operations
6. If still too slow, reduce `maxDepth` to 8
7. If still infeasible (>15 handlers, >6 state groups), use `subsystems` for compositional verification
8. Add `verification: { timeout: 300 }` to prevent runaway runs
9. **Last resort**: reduce `maxInFlight` to 1 (but know you're losing concurrency coverage)

## Visualizer (`polly visualize`)

Generates Structurizr DSL from static analysis of the codebase. Produces architecture diagrams (system context, container, component, dynamic views).

### Supported Project Types

| Type | Detection |
|------|-----------|
| Chrome Extension | `manifest.json` present |
| Monorepo | `package.json` with `workspaces` field |
| WebSocket/Server | Dependencies: `ws`, `socket.io`, `elysia`, `express`, `fastify`, `hono`, `koa` |
| Electron | `electron` dependency |
| PWA | `public/manifest.json` |
| Generic | Fallback — scans for `src/index.ts` etc. |

### Monorepo Support (v0.18)

Projects with `workspaces: ["packages/*"]` are detected automatically. Each workspace package gets a context name inferred from its package name:

| Package name contains | Context |
|---|---|
| `api`, `server`, `backend` | `server` |
| `web`, `app`, `frontend`, `client` | `client` |
| `shared`, `common`, `lib`, `core` | `shared` |
| anything else | raw package name |

Context overrides propagate to `HandlerExtractor` and `FlowAnalyzer` so files in `packages/api/src/` correctly infer as `server` context (not `unknown`).

### Handler Extraction

The analyzer extracts these handler patterns:

- **`.on()`/`.addEventListener()`** — standard event handlers
- **`if (data.type === 'value')`** — equality-check type guards in if-else chains
- **Type guard functions** — `if (isSubscribe(msg))` with resolved type predicates
- **Switch statements** — `switch (msg.type) { case 'subscribe': ... }`
- **Handler maps** — `const handlers = { subscribe: fn, unsubscribe: fn }`
- **Elysia `.ws()`** — extracts `message`, `open`, `close` callbacks; walks `message` body for sub-handlers
- **REST routes** — `.get()`, `.post()`, `.put()`, `.delete()`, `.patch()` on files importing known web frameworks (Elysia, Express, Hono, Fastify, Koa). Generates `messageType` like `"POST /todos"` with `handlerKind: "rest"`.

### False Positive Guard

REST method extraction (`.get()`, `.post()`, etc.) only activates when the source file imports from a known web framework. This prevents `Map.get()`, `Array.pop()`, etc. from being misidentified as REST endpoints.

## TLA+ Field Name Gotcha

Handlers accessing `loginState.value.loggedIn` generate TLA+ field `loginState_loggedIn`. If verification config uses `loggedIn: { type: "boolean" }`, TLC fails with "nonexistent field" error. Fix: use `loggedIn: [false, true]` in state config, or ensure field names match the generated TLA+ names.

## References

- **State API details**: Read [references/state-api.md](references/state-api.md) for complete state primitives reference, options, and verification mirror usage
- **Verification API details**: Read [references/verification-api.md](references/verification-api.md) for complete requires/ensures/$constraints/defineVerification reference with all config field types
- **Which example to reference**: Read [references/examples-guide.md](references/examples-guide.md) for feature matrix showing which example demonstrates which feature, plus links to key files

## Online Resources

- Examples: `https://github.com/AlexJeffcott/polly/tree/main/examples`
- State docs: `https://github.com/AlexJeffcott/polly/tree/main/docs/STATE.md`
- Background setup: `https://github.com/AlexJeffcott/polly/tree/main/docs/BACKGROUND_SETUP.md`
- Peer-first RFC: `https://github.com/AlexJeffcott/polly/tree/main/docs/RFC-041-peer-first.md`
- Choosing a tier: `https://github.com/AlexJeffcott/polly/tree/main/docs/RFC-041-choosing.md`
- WebRTC mesh RFC: `https://github.com/AlexJeffcott/polly/tree/main/docs/RFC-041-peer-first-webrtc.md`
- Root README: `https://github.com/AlexJeffcott/polly/tree/main/README.md`
