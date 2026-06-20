# `polly bdd` — Behaviour-Driven Development as polly's third verification stratum

Polly already derives two verification strata from one source of truth —
`{ message-handlers (types + `requires`/`ensures`), state signals }`:

- **`polly verify` (TLA+/TLC)** — exhaustive *invariants* over the handler state machine.
- **`polly mutate` (Stryker)** — *test adequacy*: are the tests actually killing mutants.

`polly bdd` adds the third, **outside-in** stratum: concrete acceptance examples *from the user's
perspective*, captured as executable Gherkin and run across the **real factory boundary**. It is the
runner a three-amigos session writes its `.feature` files into (see the global `three-amigos` skill).

## Why it links instead of bolting on

A Gherkin scenario decomposes onto the *exact same vocabulary* the other two strata already speak:

| Gherkin | Polly model |
| --- | --- |
| `Given` | an initial assignment over **state signals** (`user`, `todos`, `theme`…) |
| `When` | **one message send** — a type from the handler set (`USER_LOGIN`, `TODO_ADD`…) |
| `Then` | an **observable assertion** over signals — which should agree with that handler's `ensures()` |

## The keystone: a dual-use step binding

`defineStep()` mirrors the trick that makes `requires()`/`ensures()` work — one declaration, two
consumers. Its `given`/`when`/`then` callbacks drive the **runtime**; its `message`/`stateExpr`
strings are read **statically** by the verify cross-link.

```ts
// features/steps.ts
import { defineStep, defineWorld } from "@fairfox/polly/bdd";
import { createBackground, MessageRouter } from "@fairfox/polly/background";
import { createMockAdapters } from "@fairfox/polly/test";
import { registerTodoHandlers } from "../src/background/handlers";
import { user, todos } from "../src/background/state";

// Build the world from the DOCUMENTED factory — never a hand-wired bus (polly#57).
defineWorld({
  create() {
    MessageRouter.resetInstance();
    const bus = createBackground(createMockAdapters());
    registerTodoHandlers(bus);                       // the same helper the real entry calls
    return { bus, signals: { user, todos }, vars: {} };
  },
  reset() {                                          // cold start before every scenario
    user.value = { id: null, name: "Guest", role: "guest", loggedIn: false };
    todos.value = [];
  },
});

defineStep({
  pattern: "the user is logged out",
  given: () => { user.value = { id: null, name: "Guest", role: "guest", loggedIn: false }; },
  stateExpr: "user.loggedIn === false",              // ← formal: cross-checked against the config
});

defineStep({
  pattern: "the user logs in as {string}",
  when: (w, role) => w.bus.send({ type: "USER_LOGIN", payload: { userId: "u1", name: "U", role } }),
  message: "USER_LOGIN",                             // ← formal: must be a modeled message type
});

defineStep({
  pattern: "the user is logged in",
  then: () => { if (!user.value.loggedIn) throw new Error("expected logged in"); },
  stateExpr: "user.loggedIn === true",
});
```

Push the mechanics (which message, which signal) into the step def so the `.feature` stays
declarative — describe *what the user does and observes*, never which button.

## What each stratum can and cannot check

`requires()` is a **runtime no-op** — it exists only for the TLA+ model. So a precondition-only
negative ("a guest login is rejected") is **not runtime-observable**: at runtime the handler still
runs. Tag those scenarios `@formal`; the runner **defers** them with a note, and `polly verify` is
where they're actually checked — the `requires()` guard is extracted into the TLA+ model.
Runtime-enforced negatives (an action on a missing id that returns `{ success: false }`, a filter
that excludes a non-match) belong in the runner. That division is the point — three strata, each
doing what only it can.

A deeper formal link rides `polly verify --witness`: each scenario's Then-outcome becomes a
per-scenario TLC **reachability witness**. The witness is the negated existential `~(\E ctx : <Then>)`,
so TLC *violating* it means the outcome is reachable — the scenario is honest, and the counterexample
trace is its path through the model. A clean full exploration means the outcome is **unreachable** —
the scenario asserts a state the model proves impossible, so it lies, and the run fails. The reduction
reuses the same `stateExpr` metadata, substituting the values captured from the step text
(`their role is "admin"` + `user.role === "{0}"` → `user.role === "admin"`); a Then with no
comparison (a bare field, or a runtime-only check) has no state-observable outcome and is reported as
skipped, never silently dropped. Witnesses route to the subsystem that owns their fields and run
without the depth bound (a "reachable" verdict is sound at any bound; "unreachable" needs full
exploration, which `StateConstraint` keeps finite). The static `polly bdd check` below stays the
always-on, Docker-free gate; the witness is the opt-in, Docker-backed one.

Tag a scenario **`@forbidden`** to flip the witness into a safety check: its Then names a state that
must be *unreachable*. Same negated existential, inverted verdict — TLC finding no path is the pass
(the state is provably impossible), and TLC reaching it is the failure, with the counterexample as the
path to the defect. So the positive witness proves a desirable outcome *can* happen, and the
`@forbidden` witness proves an undesirable one *cannot*. Both `@formal` and `@forbidden` are
formal-only; the runtime runner defers them and `polly verify --witness` settles them.

### Linking to mutate

The negative-complement check is the static, Docker-free enforcer of the mutation-testing
discipline: a positive-only feature can pass against an over-permissive build (a filter that returns
*everything* still returns the match), exactly the mutant `polly mutate` would surface as a survivor.
The BDD tier is also wired into the Stryker kill matrix as its own surface (Stryker's `command` runner
over `polly bdd run`): mutate the handlers, run the scenarios, and any mutant a scenario *should* have
killed but didn't is a survivor — the mechanical complement to the negative-complement warning.

## Commands

```
polly bdd [run] [path]   Run .feature files across the real boundary (red before green)
polly bdd check          Static cross-check of every scenario against specs/verification.config.ts:
                           · every When sends a message type the config models
                           · every Given/Then names a state field the config tracks
                           · every filtering/selecting feature has a negative complement
polly bdd new <name>     Scaffold a .feature stub seeded from the verify vocabulary
```

Conventions (override with `--features` / `--steps`): features at `features/**/*.feature`, step
modules at `features/**/*.steps.ts` and `features/steps.ts`.

## The boundary rule

Build the world through the **documented factory** (`createBackground`, `createMeshClient`), from
**cold state**, exactly as a real consumer would — never a hand-wired bus that silently compensates
for a gap the real path has (the polly#57 lesson). For features that cross a process/network/device
boundary, drive the real e2e kit (`tools/test/src/e2e-mesh`) from the step definitions; the scenario
stays declarative.

`scripts/mesh-bdd/sync.feature` is that shape realised: a two-device convergence scenario whose
world is a *page driver*. Its `defineWorld.create()` boots a real relay and two cold browser peers
through `createMeshClient`, the steps drive Puppeteer pages and `waitForConvergence`, and the
optional `defineWorld.teardown(world)` closes the browsers and relay so the runner exits cleanly.
Resources that outlive a scenario live at module scope, not in `world.vars` — the runner wipes
`vars` before every scenario as per-scenario scratch.
