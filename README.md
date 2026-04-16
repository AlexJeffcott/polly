# @fairfox/polly

Reactive state for multi-context apps — from single-process signals to peer-to-peer encrypted mesh — with formal verification.

## The pitch

Define state once. Read it anywhere. Polly keeps them in sync.

```typescript
// src/shared/state.ts
import { $sharedState } from "@fairfox/polly/state";

export const counter = $sharedState("counter", 0);
```

```typescript
// src/background/index.ts — service worker, extension background, Node process
import { createBackground } from "@fairfox/polly/background";
import { counter } from "../shared/state";

const bus = createBackground();

bus.on("INCREMENT", () => {
  counter.value++;
  return { count: counter.value };
});
```

```typescript
// src/popup/index.tsx — browser popup, any Preact/React UI
import { render } from "preact";
import { counter } from "../shared/state";

function App() {
  return (
    <div>
      <p>Count: {counter.value}</p>
      <button onClick={() => counter.value++}>+</button>
    </div>
  );
}

render(<App />, document.getElementById("root")!);
```

The background writes `counter`. The popup reads it. Both stay in sync — no message passing, no subscriptions to manage. State is a [Preact Signal](https://preactjs.com/guide/v10/signals/), so the UI re-renders automatically when the value changes.

## State that syncs everywhere

Modern apps run code in multiple isolated contexts: service workers, content scripts, server processes. Keeping state consistent across them means writing sync logic for every piece of data. Polly replaces that with four primitives:

| Primitive | Syncs | Persists | Use for |
|-----------|:-----:|:--------:|---------|
| `$sharedState` | yes | yes | User data, settings, auth — anything that should survive a restart and stay consistent |
| `$syncedState` | yes | no | Ephemeral shared state: connection status, live collaboration flags |
| `$persistedState` | no | yes | Per-context settings, form drafts |
| `$state` | no | no | Local UI state: loading spinners, modal visibility |

All four return Preact Signals. Read with `.value`, write with `.value =`.

```typescript
import { $sharedState, $syncedState, $persistedState, $state } from "@fairfox/polly/state";

const user = $sharedState("user", { name: "Guest", loggedIn: false });
const wsConnected = $syncedState("ws", false);
const draft = $persistedState("draft", "");
const loading = $state(false);
```

For async data, `$resource` fetches and re-fetches automatically when its dependencies change:

```typescript
import { $resource } from "@fairfox/polly/resource";

const todos = $resource("todos", {
  source: () => ({ userId: user.value.id }),
  fetcher: async ({ userId }) => {
    const res = await fetch(`/api/todos?userId=${userId}`);
    return res.json();
  },
  initialValue: [],
});

todos.data;   // Signal<Todo[]>
todos.status; // Signal<"idle" | "loading" | "success" | "error">
todos.refetch();
```

## Peer-first state (v0.21.0)

The four primitives above keep state consistent inside a single deployment. But some applications need state that survives the server going away, or state that the server never sees at all. Polly now offers three resilience tiers, each a distinct primitive family:

| Tier | Primitive | Server's role | Resilience |
|------|-----------|---------------|------------|
| Weakest | `$sharedState` | Source of truth | Server backups |
| Middle | `$peerState` | Full peer on the data path | Any device can rehydrate the server |
| Strongest | `$meshState` | Not on the data path | App works with zero server uptime |

**`$peerState`** — every device holds a full [Automerge](https://automerge.org/) CRDT replica. The server holds one too, so cron and HTTP handlers can read and mutate documents. If the server loses its storage, any reconnecting client repopulates it through the normal sync protocol.

```typescript
import { createPeerStateClient, configurePeerState, $peerState } from "@fairfox/polly";

const client = createPeerStateClient({ url: "wss://yourapp.com/polly/peer" });
configurePeerState(client.repo);

const settings = $peerState("settings", { theme: "dark" });
await settings.loaded;
settings.value = { theme: "light" }; // syncs to every peer
```

**`$meshState`** — peers exchange operations directly over WebRTC data channels, signed with Ed25519 and encrypted with XSalsa20-Poly1305. No server sees the data. A small stateless signalling server helps peers find each other; removing it does not affect running connections.

```typescript
import { configureMeshState, $meshState, MeshNetworkAdapter, MeshWebRTCAdapter } from "@fairfox/polly";

const repo = new Repo({ network: [new MeshNetworkAdapter({ base: webrtcAdapter, keyring })] });
configureMeshState(repo);

const notes = $meshState("notes", { entries: [] });
// Operations flow peer-to-peer, signed and encrypted
```

First-time key exchange between devices uses a pairing token displayed as a QR code. Compromised devices are revoked via signed revocation records that propagate to every peer.

The three tiers coexist in one application — public settings in `$sharedState`, collaborative documents in `$peerState`, private notes in `$meshState`. See [docs/STATE.md](docs/STATE.md) for the full decision tree and [docs/RFC-041-choosing.md](docs/RFC-041-choosing.md) for the design rationale.

## Verification that plugs in

A popup and a background script both write to the same state. A content script reads it mid-update. Tests miss these bugs because they depend on timing.

Polly generates [TLA+](https://lamport.azuretext.org/tla/tla.html) specifications from your existing state and handlers, then model-checks them with TLC. You don't learn a new language. You annotate what you already wrote.

### Step 1: Add contracts to handlers

`requires()` and `ensures()` are runtime no-ops. `polly verify` reads them statically.

```typescript
import { createBackground } from "@fairfox/polly/background";
import { requires, ensures } from "@fairfox/polly/verify";
import { user, todos } from "./state";

const bus = createBackground();

bus.on("TODO_ADD", (payload: { text: string }) => {
  requires(user.value.loggedIn === true, "Must be logged in");
  requires(payload.text !== "", "Text must not be empty");

  todos.value = [...todos.value, {
    id: Date.now().toString(),
    text: payload.text,
    completed: false,
  }];

  ensures(todos.value.length > 0, "Todos must not be empty after add");

  return { success: true };
});
```

### Step 2: Define state bounds

A verification config tells TLC what values to explore:

```typescript
// specs/verification.config.ts
import { defineVerification } from "@fairfox/polly/verify";

export const verificationConfig = defineVerification({
  state: {
    "user.loggedIn": { type: "boolean" },
    "user.role": { type: "enum", values: ["guest", "user", "admin"] },
    todos: { maxLength: 1 },
  },
  messages: {
    maxInFlight: 2,
    maxTabs: 1,
  },
});
```

### Step 3: Run it

```
$ polly verify

Generating TLA+ specification...
Running TLC model checker...

  Model checking complete.
  States explored: 1,247
  Distinct states: 312
  No errors found.

All properties verified.
```

If a `requires()` can be violated — say, a logout races with a todo add — TLC finds the exact sequence of steps that triggers it.

For larger apps, [subsystem-scoped verification](https://github.com/AlexJeffcott/polly/tree/main/examples/todo-list) splits the state space so checking stays fast.

## Quick start

```bash
bun add @fairfox/polly preact @preact/signals
```

Scaffold a project:

```bash
polly init my-app --type=extension  # or: pwa, websocket, generic
```

Or start from one of the examples:

```bash
git clone https://github.com/AlexJeffcott/polly.git
cd polly/examples/minimal
bun install && bun run dev
```

## Examples

| Example | What it demonstrates |
|---------|---------------------|
| [minimal](examples/minimal) | Counter with `$sharedState` — the simplest possible Polly app |
| [todo-list](examples/todo-list) | CRUD with `requires()`/`ensures()`, subsystem-scoped verification |
| [full-featured](examples/full-featured) | Production Chrome extension with all framework features |
| [elysia-todo-app](examples/elysia-todo-app) | Full-stack web app with Elysia + Bun, offline-first |
| [webrtc-p2p-chat](examples/webrtc-p2p-chat) | Peer-to-peer chat over WebRTC data channels |
| [team-task-manager](examples/team-task-manager) | Collaborative task management with end-to-end encryption |

## CLI

```
polly init [name]       Scaffold a new project
polly build [--prod]    Build for development or production
polly dev               Build with watch mode
polly check             Run all checks (typecheck, lint, test, build)
polly typecheck         Type-check your code
polly lint [--fix]      Lint (and optionally auto-fix)
polly format            Format your code
polly test              Run tests
polly verify            Run formal verification
polly visualize         Generate architecture diagrams (Structurizr DSL)
```

## Quality tooling

Polly ships conformance checks and a browser test harness that consuming applications can adopt directly.

**No-as-casting check.** Bans TypeScript `as` type assertions codebase-wide (only `as const` and the explicit escape hatch `as unknown as` are allowed). Violations include pattern-specific fix advice. Import it programmatically:

```typescript
import { checkNoAsCasting } from "@fairfox/polly/quality";

const result = await checkNoAsCasting({ rootDir: process.cwd() });
if (result.violations.length > 0) {
  result.print();
  process.exit(1);
}
```

**Browser test harness.** A Puppeteer-based harness for testing browser-only code (WebRTC adapters, Preact components, anything needing real DOM). Bundles each test file with Bun.build, serves on an ephemeral port, and collects results:

```typescript
import { describe, test, expect, done, flush, cleanup } from "@fairfox/polly/test/browser";

describe("my component", () => {
  test("renders", async () => {
    render(<MyComponent />, app);
    await flush();
    expect(app.querySelector("h1")).toHaveTextContent("Hello");
    cleanup(app);
  });
});

done();
```

Run with `bun tools/test/src/browser/run.ts tests/browser`.

## Use with Claude Code

This repo ships with a [Claude Code skill](.claude/skills) that covers the full Polly API — state primitives, peer-first and mesh state, verification, quality tooling, and the browser test harness. Install it in your project so Claude can help you integrate Polly with full context:

```bash
# From your project directory
claude install-skill /path/to/polly/.claude/skills
```

Then ask Claude things like:
- "How would Polly fit into this project?"
- "Add verification to my handlers"
- "Set up $peerState with an Elysia server"
- "Wire up the no-as-casting conformance check in CI"

If you maintain your own Claude Code skills, consider adding Polly's state-tier decision tree and verification patterns to your project-specific skill so Claude can recommend the right primitive for each piece of state.

## Licence

MIT

---

[GitHub](https://github.com/AlexJeffcott/polly) &middot; [Issues](https://github.com/AlexJeffcott/polly/issues) &middot; [Examples](https://github.com/AlexJeffcott/polly/tree/main/examples)
