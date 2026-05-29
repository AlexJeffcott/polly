# test-debt

Finds **dead weight in the test suite** — the inverse of mutation testing.
Where Stryker tells you what code no test pins (surviving mutants), this reads
the same kill matrix the other way and tells you which tests pin nothing the
rest of the suite doesn't already pin.

The motivating observation: above ~90% mutation score the score stops being
informative (everyone's saturated) and the interesting number becomes *how
much suite you spend to hold it*. On zws today that's a 7.6× case-level
redundancy ratio — 106 killing tests doing the work of ~14.

## Signals

| signal | meaning | data needed |
|---|---|---|
| **gaps** | survived mutants — code no test pins | status |
| **redundancy** | tests/files whose every kill is caught elsewhere too | `killedBy` matrix |
| **theatre** | covered-but-survived — assertions ran the code but caught nothing | coverage `"all"` |

Redundancy is reported at both **file** and **case** level. Decisions should be
keyed at file level — file identity is stable across `describe` restructuring,
git tracks renames — with the case list as drill-down.

## Usage

```sh
bun run mutation             # produce reports/mutation/mutation.json
bun run test-debt            # print the signals report
bun run test-debt:decisions  # join signals against the committed decisions log
bun run test-debt:verify     # run a fresh pass + assert the matrix contract
```

### Decisions log

Signals are derived and regenerable; **decisions** about them are not, and live
in `decisions.jsonl` (committed, mergeable, append-only, last-write-wins per
file). Record one with:

```sh
bun scripts/test-debt/decisions.ts decide <test-file> <keep|prune|rewrite|investigate> "<rationale>"
```

`decisions.ts` (default `status`) joins the fresh matrix against the log and
buckets every file into **needs-review** (subsumed, no decision yet), **stale**
(the decision's basis drifted), or **settled** (decision still holds — kept off
the action list). Each decision stores a normalised content hash of the test
file *and* its subsumption snapshot at decision time; a verdict goes stale when
the file changes (real edits only — comments/formatting are normalised out) or
when the matrix around it shifts (e.g. a test elsewhere is deleted, making this
file's kills newly unique). That's what stops a `keep` from outliving its
reason.

The SQLite db (`reports/test-debt.sqlite`) is a **regenerable build artefact**
— gitignored. The tool consumes the mutation-testing-report **schema**, never a
specific runner, so the analysis is portable to any matrix-producing runner.

## How the matrix is produced (the fragile part)

Bun has no Stryker plugin and the `command` runner can't report per-test
results, so there's no kill matrix by default. We use the community
`stryker-mutator-bun-runner`, **pinned to 0.4.0 and patched** (`bun patch`,
diff committed under `patches/`). Plugin 0.4.0 predates Bun 1.3.x and was
broken against it; the patch:

1. **Emits + parses JUnit XML** (`--reporter=junit --reporter-outfile`). Bun
   1.3.x prints no per-test console lines when piped and has no TAP reporter,
   so the plugin's console-scraping parser found zero tests. JUnit is the only
   machine-readable per-test source Bun exposes.
2. **Carries `fileName`/`startPosition`** into each test result, so the report
   is keyed by real test-file paths instead of one `""` bucket — file-level
   identity.
3. **Disables the per-mutant bail** so `killedBy` lists *every* killing test,
   not just the first — without this the redundancy signal is dead.
4. **Extracts coverage from the Bun child.** The plugin's collector read
   `__stryker__` in the *runner* process, where it's always empty — the
   instrumented code runs in the Bun child. The patch dumps
   `__stryker__.mutantCoverage` from a global `afterAll` (Bun's `bun test`
   doesn't fire `process` exit events in preloads) and the adapter reads it
   back. That makes coverage `"all"` work, which is what splits gaps (NoCoverage)
   from theatre (Survived).

This rests on a pinned pair: **(Bun version, plugin+patch)**. A Bun upgrade or a
patch that stops applying can silently collapse the matrix. `verify-matrix.ts`
is the guard — run it after any bump.

`coverageAnalysis` is `"all"`: Stryker then runs only covered mutants, marking
the rest **NoCoverage** (true gaps) and leaving covered-but-undetected ones
**Survived** (theatre). That status split *is* the gap/theatre distinction —
flip coverage to `"off"` and it's lost (everything non-killed shows as
Survived). Per-mutant `coveredBy` (which *specific* tests cover a theatre mutant
— the rewrite target) still needs per-test coverage and is not yet wired; the
file/suite-level theatre signal works today.

## Caveats — the matrix nominates, a human convicts

- **Redundant ≠ useless.** Mutation operators only model the faults they model.
  A test subsumed against today's mutants can still be the only guard against a
  fault class the operators never generate, or valuable as documentation.
- **Don't minimise to 1.** A minimal cover leaves every mutant killed by exactly
  one test — no defence-in-depth. Prune toward an N-cover (every mutant killed
  ≥ N times), not the greedy minimum the ratio reports.
- The greedy "~N prunable" is an upper bound on surplus, not a delete list.

## Polly notes (monorepo specifics)

- **Scope.** `mutate` covers 20 `shared/lib` modules: the 13 pure-logic primitives
  plus the mesh I/O stack (`signing`, `mesh-diagnostics`, `peer-relay-adapter`,
  `mesh-signaling-client`, `mesh-network-adapter`, `mesh-client`,
  `mesh-webrtc-adapter`) brought in once coverage `"all"` made uncovered paths free
  (instant NoCoverage) — polly#124 Phase 3. `mesh-state.ts` stays out: its seed path
  is guarded by a dedicated runtime determinism test and a TLA+ spec, and its lazy
  factory is timing-bound (see polly#124 Phase 2 / `tools/verify/MUTATION-ORACLE-SPIKE.md`).
  The mesh modules surfaced large gaps. `mesh-signaling-client` was 0% (no test
  executed it) and has since been brought to 86% with a fake-WebSocket suite;
  `peer-relay-adapter` is still 0%, and `mesh-client` / `mesh-webrtc-adapter` carry
  hundreds of NoCoverage + Survived mutants. Surfacing those was the measurement
  Phase 3 set out to take; closing the remaining gaps is follow-up work.

- **Timeouts inflate runtime.** Mutating async/retry code in `signing` (36) and
  `mesh-network-adapter` (41) produces hangs that only resolve at `timeoutMS` (90s).
  They score correctly (a timeout is a detected mutant) but stretch the 20-module run
  to ~90min. Raising concurrency or lowering `timeoutMS` trades wall-clock against the
  risk of flagging a slow-but-correct test as a false timeout-kill.

- **Two test directories, run from the repo root.** Stryker's bun runner spawns
  `bun test` from the sandbox root, not `packages/polly`, so `bun.testFiles` are
  repo-root globs (`packages/polly/tests/unit/**`, `packages/polly/src/**`). Six
  UI/action test files (`tests/unit/actions/*`, `polly-ui-components.test.ts`)
  **do not load** from that cwd: Bun resolves the JSX runtime against the nearest
  tsconfig to the cwd, and with no root tsconfig it defaults to `react` instead of
  the package's `jsxImportSource: preact`, so the TSX imports fail. These six are
  excluded from the matrix (76 of 82 test files present). Verified harmless: the
  per-module kill counts are identical to the command-runner baseline (which ran
  all 82 from `packages/polly`), so the excluded files kill nothing in the mutated
  set. `bun.command` can't fix this — it disables the patch's JUnit emission, which
  is the matrix — and the plugin doesn't pass `cwd` to the spawn.

- **All mutants are "static".** The patch reports coverage as a single
  `mutantCoverage` dump, not per-test, so Stryker can't filter tests per mutant and
  marks every covered mutant static — the full suite runs for each. Expected (the
  per-test `coveredBy` rewrite target is out of scope here). Leave `ignoreStatic`
  off, or the covered mutants are skipped entirely.
