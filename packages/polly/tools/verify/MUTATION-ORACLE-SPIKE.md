# TLA+ as a mutation oracle — spike conclusion (polly#124 Phase 2)

**Verdict: rejected, with reason.** Do not wire `polly verify` into the Stryker
kill-path. The formal verifier checks specifications that are decoupled from the
implementation code Stryker mutates, so it kills almost nothing the unit suite
misses — and on the one invariant the issue named, it misses the same mutant the
unit suite does.

## The question

> Does mutating `mesh-state.ts` `seedDocumentBytes` to a non-deterministic seed
> get killed by the verifier (the #113 seed-race invariant) when it might survive
> the unit suite?

## The experiment

Applied a faithful Stryker mutation to `seedDocumentBytes` — the `ObjectLiteral`
mutator turns `Automerge.change(empty, { time: 0 }, …)` into
`Automerge.change(empty, {}, …)`. Dropping `time: 0` lets the change timestamp
fall back to `Date.now()`, which is exactly the pre-#113 regression: two devices
seeding the same logical key at different instants produce different bytes and
diverge.

| Oracle | Command | Result |
|---|---|---|
| Unit suite | `bun test ./tests/unit ./src` | **1009 pass, 0 fail — mutant survives** |
| TLA+ verifier | `bun scripts/e2e-verify-mesh-seed.ts` | **passes unchanged — mutant survives** |

Both oracles let the regression through.

## Why the verifier can't see it

`MeshSeed.tla`'s `SeedDeterministic` constant is flipped by the
`POLLY_113_DISABLE_FIX` *environment variable*, not by reading `seedDocumentBytes`
(`meshSeedCfg` / `isSeedFixDisabled` in `tools/verify/src/runner/mesh-seed.ts`
rewrite the `.cfg` from the env var). TLC runs against a hand-written `.tla` file;
it never imports or executes the mutated module. A source mutation does not set
the env var, so the verifier runs with `SeedDeterministic = TRUE` and passes
regardless of what the implementation does.

This generalises beyond the seed path. Stryker mutates the 13 `shared/lib`
primitive modules. The TLA+ extractor reads handler logic and `requires`/`ensures`
expressions from *application* code, not the internals of these library
primitives — so no mutation of the mutated set changes the generated spec. And the
`requires`/`ensures` expressions the extractor *does* read are the runtime no-ops
that the polly#143 ignorer deliberately excludes from mutation. The set of
mutations TLC could catch and the set Stryker introduces barely intersect.

## Cost (secondary)

For the tiny hand-written `MeshSeed` spec TLC is ~1s per run — cheap. But the
*generated* specs run for minutes (full-featured >2min, mesh >7min), and Stryker's
command runner cannot filter tests per mutant, so a per-mutant verifier loop over
those specs would take hours to days. The capability gap makes the cost question
moot: even where TLC is fast, it kills nothing extra.

## What would catch the regression

A **runtime determinism assertion**: seed the same logical key on two peers at
different wall-clock times and assert byte-identical output. That is a unit/e2e
concern, not a TLC one. `e2e-verify-mesh-seed.ts` proves the *model* is sound and
that the env-toggle path is wired, but by construction it cannot detect
implementation drift in `seedDocumentBytes`, because it is gated on the env var
rather than the code. The honest follow-up is a runtime seed-determinism test —
that is the oracle that would have killed this mutant.

## Acceptance

- Phase 2 spike conclusion: **rejected-with-reason** (above).
- Reproduce: apply the `{ time: 0 }` → `{}` edit to `seedDocumentBytes`, run the
  two commands in the table, observe both pass, revert.
