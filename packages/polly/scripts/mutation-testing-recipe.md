# Mutation testing — recipe

Polly's test suite is the only automated gate before a TOTP-protected
manual `npm publish`. Mutation testing is how we periodically verify
the gate is still load-bearing: deliberately introduce subtle bugs,
run the suite, and pay attention to which ones slip through. The
survivors are the gaps to close.

The four round files in `docs/mutation-testing/round-{1..4}.md` are
the historical record of the first run. This file is the recipe so
future runs are faster.

---

## Method

For each round, pick **5 mutations**. For each mutation:

1. Apply the change with `Edit`.
2. Run `bun run --cwd tests test`.
3. Record: which tests failed (if any), how long the suite ran, what
   the failure mode was (assertion mismatch, timeout, type error).
4. Revert with `Edit`.
5. Verify the suite returns to baseline before the next mutation.

Five mutations per round, ~5 minutes per mutation, ~25 minutes per
round. The first run did four rounds in ~2 hours total, including
the per-round writeups.

Picking 5 by hand is the whole skill of the exercise. Mutation tools
like Stryker generate everything mechanically — most of it noise.
Hand-picking targets the codepaths where a subtle bug would
plausibly land in production. The catch rate of the first run rose
from 40 % (round 1) to 80 % (round 3) as the operator learned where
the suite was thin.

---

## Good targets

Categories that produced high-signal mutations across the four rounds:

- **Security primitives.** signing, encryption, revocation, pairing.
  A surviving mutation here is a forge or a bypass.
- **Boundary comparators.** `>`, `<`, `>=`, `<=` in conditions on
  user-provided or time-derived values. The `>` ↔ `>=` flip is the
  most common off-by-one in the codebase.
- **Cross-field invariants.** Functions that assert a relationship
  between two fields of the same data structure (e.g.
  `decodeRevocation`'s "envelope sender matches payload issuer"
  cross-check). Tests rarely build the discordant fixture.
- **Loop bounds.** Loops over collections where every existing test
  fixture has `length === 1`. Mutations that truncate the iteration
  to one go undetected.
- **Side-effect-vs-value.** Functions that emit a log/warn AND
  return a value. Tests often assert on the side-effect; the return
  value can be wrong.
- **Load-bearing utilities.** Any function imported by many call
  sites with no dedicated test file. Callers trust the name; the
  contract is implicit.
- **Cross-subsystem properties.** Domain separation, cross-primitive
  identity. Per-module tests can't observe these.

## Mutation patterns that catch real bugs

| Pattern | Example | Survival rate (first run) |
|---|---|---|
| Drop a security cross-check | `revocation.ts:339` | high |
| Truncate a loop to first element | `for (... of arr.slice(0,1))` | high |
| Flip a boundary comparator | `>` ↔ `>=` | mixed (depends on test) |
| Invert a return-value sentinel | `success: false` → `success: true` | high |
| Swap two fields | `{ pub: ..., priv: ... }` | low (round-trip catches) |
| Drop a load-bearing guard | a `continue` becomes a fallthrough | mixed |
| Drop domain prefix on a hash | `hash("ns:" + key)` → `hash(key)` | high |
| Replace `.shift()` with `.pop()` | wrong end of buffer evicted | low |

---

## Cadence

Run the recipe:

- **Every 4–5 minor versions.** If the last full run was at 0.39.0,
  next at ~0.43.0 or whenever a security-relevant module changes.
- **Whenever a security-relevant module changes** —
  `revocation.ts`, `signing.ts`, `pairing.ts`,
  `mesh-network-adapter.ts`, `encryption.ts`, `keyring-storage.ts`.
- **After a test-harness restructuring** — to confirm the new
  arrangement still has the same coverage as the old one.

Don't run after every bug fix. The signal is in the human picking
the targets; running it on autopilot dilutes that.

---

## Output format

For each round, write a markdown file at
`docs/mutation-testing/round-{N}.md` with this shape:

```markdown
# Mutation Testing — Round N

Targets: <list of modules>

| #  | File | Category | Result |
|----|------|----------|--------|

## Mutation N — <file>: <one-line description>
**Location:** <file:line>
**Change:** <what the mutation did>
**Result:** caught / SURVIVED. <test count, runtime>
**Why it survived:** (if applicable)
**Severity:** low / medium / high
**Test gap:** <what's missing>

## Round-N Findings
<patterns observed across the round>
```

If you do four rounds, write a fifth file at
`docs/mutation-testing/summary-<date>.md` synthesising the
categories of survivor and ranking by severity. Keep the historical
artifacts; future maintainers need to see what was found and what
the response was.

---

## Closing survivors

The first-run survivors and their closures landed in 0.39.0:

| Survivor | Closure |
|----------|---------|
| revocation cross-check | tests/unit/revocation.test.ts |
| message-router multi-target | tests/unit/message-router.test.ts |
| crdt-state cycle (stale assertion) | tests/unit/crdt-state.test.ts (heads invariant) |
| mesh-state domain separation | tests/unit/mesh-state.test.ts |
| message-bus silent success | tests/unit/message-bus.test.ts |
| pairing expiry boundary | tests/unit/pairing.test.ts |
| Lamport `>` boundary | tests/unit/state.test.ts |
| deepEqual mismatched keys | tests/unit/state.test.ts |
| isRecord array exclusion | tests/unit/guards.test.ts |

`docs/mutation-testing/round-{1..4}.md` documents the original
survivors and their analysis. Future runs that expose new survivors
should be added to that record, not replace it.

## What good looks like

A round where every mutation is caught. That's not the goal of any
single round — the value comes from the survivors — but it's the
shape the suite should converge toward over many rounds.

A round where >50 % survive, on the other hand, is a signal that
the suite has decayed. Stop the round, raise the issue, decide
whether to invest in tests before continuing.

The first-run rounds had survival rates 60 % / 40 % / 20 % / 60 % —
average 45 %. After 0.39.0 ships, expect the next run to land in
the 10–25 % range.
