# Off-surface state mutators (polly#163)

## What this is

The verifier models a system as **dispatched, guarded transitions** — message
handlers extracted from `bus.on(...)`, switch/type-guard dispatch, ws/rest
routes, and (since Issue #27) *exported top-level* state-mutating functions.
Each becomes a TLA+ action with a precondition (`requires`), an effect
(assignments), and an optional postcondition (`ensures`). TLC explores those
actions exhaustively.

A verified-state write that is **not** inside any of those is *off-surface*: a
class/object method, a non-exported function, or a nested closure that writes
`signal.value` / `signal.value.field` directly. The model has no action for it,
so:

- TLC never explores the state it produces;
- mutation testing has no line in a modelled path to mutate;
- the #162 model-coverage report can't count it — and when a real handler
  *also* writes the field, the field is not "unwritten", so #160's
  `unwrittenFields` signal stays silent.

This is the exact shape of the #160 bug: a `register()` recovery path that set
`canSend` (a capability) without going through a dispatched, guarded handler.

## How it is detected

`HandlerExtractor` records the source span of every function body it turns into
a handler (the two chokepoints: `extractAssignments` for dispatch/ws/rest/
type-guard/switch bodies, and `findStateMutationsInFunction` for the Issue #27
lift). A third pass then scans application source for `signal.value[.field] =`
writes — scoped to genuine state-signal declarations (`$state`, `$sharedState`,
`$syncedState`, `$persistedState`, `$meshState`, `$peerState`) — and reports any
whose position is outside every recorded span. Test, spec, BDD-feature, story
and e2e files are excluded: seeding state directly in a fixture is expected, not
a runtime escape.

`computeModelCoverage` folds the findings in: each declared field gains an
`offSurfaceWriters` list, and `report.offSurfaceMutations` carries the findings
that land on a **declared** field. Writes to undeclared signals are dropped —
for a signal the model does not track there is no transition to be "outside" of,
so reporting them would be noise. Under `--strict`, a declared off-surface write
is a fail-closed reason, distinct from `unwrittenFields`.

## The decision: convention (a), not auto-lift (b)

#163 framed two options for how off-surface mutators *should* be modelled:

- **(a)** require capability-establishing paths to go through a dispatched
  handler — enforce by convention (lint + `--strict` gate);
- **(b)** extend the extractor to lift an arbitrary off-surface mutator into a
  TLA+ action so the checker explores it.

**We chose (a).** The verifier reports the off-surface write and pushes the
author to make the path first-class — route the capability change through a
dispatched, guarded handler (so it gets a message, a `requires`, an `ensures`),
or drop the field from the verified surface. Reasoning:

1. **(b) is unsound for arbitrary mutators.** Issue #27 already lifts the one
   case where a lift is sound: an *exported, named, top-level* function with
   inferable parameters and a clear identity. Lifting a method, a nested
   closure, or top-level module code has no dispatch entry point — no message,
   no precondition, no actor/route, no well-defined "when does this fire". The
   synthesized action would be enabled in every state, which both invents
   counterexamples (over-approximation) and can *mask* the real bug by making
   the offending state reachable "legitimately". The whole point of the model is
   that capability transitions are dispatched and guarded; auto-lifting an
   unguarded write contradicts it.

2. **The sound resolution is to surface, not to model.** A capability granted by
   a path with no precondition is usually the bug, not a modelling gap to paper
   over. Making it visible (warn by default, fail-closed under `--strict`) is
   the behaviour that catches #160-class omissions; silently lifting it is the
   behaviour that hides them.

3. **It composes with what already exists.** `unwrittenFields` (#160) catches a
   declared field *no* path writes; off-surface detection (#163) catches a
   declared field a *non-dispatched* path writes — including the dangerous case
   where a handler writes it too. Together they make the writer set of every
   declared field complete.

### When (b) could still apply

A narrow future extension could lift a *named, exported-but-not-top-level*
mutator with inferable parameters into an action — the same soundness envelope
as Issue #27, just reached through a different declaration site. That is out of
scope here and is not required to close #163: the acceptance criteria are met by
detection + reporting + writer-set folding + this decision.
