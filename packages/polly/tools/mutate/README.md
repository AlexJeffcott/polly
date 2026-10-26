# test-debt

Finds **dead weight in the test suite** — the inverse of mutation testing.
Where mutation testing tells you what code no test pins (surviving mutants), this reads
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
| **contracts** | mutants only a `requires`/`ensures` caught, kills per contract, and contracts whose handler ran yet never fired | `killedByContract` (bun engine, `--mode matrix`, contracts on) |

Redundancy is reported at both **file** and **case** level. Decisions should be
keyed at file level — file identity is stable across `describe` restructuring,
git tracks renames — with the case list as drill-down.

## Usage

Shipped as the `polly mutate` command — consumers get it via `@fairfox/polly`, and
the pure analysis pieces are importable from `@fairfox/polly/mutate`:

```sh
polly mutate init            # write a polly.mutate.ts for this project
polly mutate migrate         # print the polly.mutate.ts equivalent of stryker.conf.json (--write writes it)
polly mutate run             # run the Bun-native engine, then print the signals report
polly mutate report          # print the signals from an existing mutation.json
polly mutate decisions       # join signals against the committed decisions log
polly mutate verify          # assert the matrix contract (--run for a fresh pass)
```

The redundancy/subsumption sections need a **complete** kill matrix (`--mode
matrix`). Without it `report`/`run` degrade to score + gaps +
theatre and print a warning; `verify` reports the broken contract.

In this monorepo the same code also backs the root scripts:

```sh
bun packages/polly/cli/polly.ts mutate run   # produce reports/mutation/mutation.json
bun run test-debt            # = polly mutate report
bun run test-debt:decisions  # = polly mutate decisions
bun run test-debt:verify     # = polly mutate verify --run
```

### Config: `polly.mutate.ts`

```ts
import { defineMutation } from "@fairfox/polly/mutate";

export default defineMutation({
  targets: ["src/**/*.ts", "!src/**/*.test.ts"], // globs, ! exclusions, a.ts:10-20 ranges
  tests: { include: ["tests/**/*.test.ts"], preload: ["./tests/setup.ts"] },
  // runner: { kind: "command", argv: ["bun", "run", "bdd"] }, // instead of `tests`
  mode: "fast",                                  // or "matrix"
  coverage: "dynamic",                           // or "static" (import graph only)
  concurrency: 6,                                // default: cores − 1
  timeout: { factor: 2, extraMs: 3000 },         // per mutant: baseline × factor + extraMs
  mutators: { exclude: ["StringLiteral"] },
  ignoreVerifyCallsites: true,                   // requires/ensures mutants → Ignored (polly#143)
  typecheck: true,                               // mutants the tsconfig rejects → CompileError, never run
  thresholds: { break: 60 },                     // `run` exits 1 below this score
  report: "reports/mutation/mutation.json",
  decisions: ".polly/test-debt/decisions.jsonl",
});
```

Paths are relative to the config's directory, which is where the tests run.
CLI flags (`--mode`, `--concurrency`, `--report`, …) override the file. The CLI
loads `./polly.mutate.ts`, else `--config <path>`; without either it falls back
to a discovered `stryker.conf.json`, read through the same mapping `polly mutate
migrate` writes out, and prints a deprecation notice.

| `stryker.conf.json` | `polly.mutate.ts` |
|---|---|
| `mutate` | `targets` |
| `bun.testFiles` | `tests.include` |
| `bun.nodeArgs` `--preload` | `tests.preload` |
| `testRunner: "command"`, `commandRunner.command` | `runner: { kind: "command", argv }` (shell syntax → `sh -c`) |
| `concurrency` | `concurrency` |
| `timeoutFactor`, `timeoutMS` | `timeout.factor`, `timeout.extraMs` |
| `disableBail` | `mode: "matrix"` |
| `mutator.excludedMutations` | `mutators.exclude` |
| `thresholds.break` | `thresholds.break` |

Every other key is Stryker machinery; `migrate` lists the ones it drops.

### The Bun-native engine (the default)

`polly mutate run` runs mutation testing on Bun alone; Stryker is no longer
used or supported (see "Comparing with Stryker" below). It writes
`reports/mutation/mutation.json` in mutation-testing-report-schema, so `report`, `decisions` and `verify` work on
its output unchanged.

| Step | How |
|---|---|
| Generate | `oxc-parser` spans; Stryker-named operators (`engine/operators.ts`); type-only syntax is never mutated; mutants inside verify primitives are reported `Ignored` (polly#143), and so are mutants a disable comment covers (see "Disable comments" below) |
| Coverage | One pass before any mutant runs: every test file once, split over `concurrency` processes, with each target served probed (`engine/probes.ts`: a hit call before the statement, inside the block, or around the expression that holds each mutant; no line moves). Hits are bucketed per test by global `beforeEach`/`afterEach` hooks and matched to junit order. A mutant no test ran is `NoCoverage`, decided without a run. Each mutant's `coveredBy` lists the tests that ran it |
| Select | Per mutant: the tests that ran it (`bun test -t`), or whole files for code that runs between tests or at module load. `--coverage static` (or a target the pass could not probe) selects the test files whose import closure reaches the target, through Bun's own resolver |
| Baseline | The selected files run once unmutated; they must pass (3 tries), and their time sets each mutant's timeout (2× + 3 s) |
| Typecheck | A mutant the project's TypeScript config rejects is `CompileError`, never run (`engine/typecheck.ts`): one `tsgo` process (TypeScript 7.1 through `typescript-7/async`, the `typescript-7` optional peer dependency) serves each mutant as the target's text in a temporary snapshot layered on the unmutated one (`typescript-7/fs` request layers, no disk writes) and reads the target's own diagnostics; the project opens through a virtual config beside the nearest `tsconfig.json` that lists the target, with `allowUnreachableCode`, `noUnusedLocals` and `noUnusedParameters` relaxed (mutants make code unreachable and bindings unused by design). The verdict is relative to the unmutated file's errors, so a target that already fails to type-check still gets a filter and never a false `CompileError`. The reason is the first new error (`TS2322: Type '""' is not assignable …`). Runs while the baselines run (44 targets: 34.6 s in one process on TypeScript 7.0.2, 43.7 s on 7.1.0-beta with identical verdicts, `scripts/mutate-typecheck-parity.ts`; the fast run went from 286 s to 244 s because 1,848 fewer mutants ran). A target with no `tsconfig.json` runs unfiltered, and the run says so. `--no-typecheck` or `typecheck: false` turns it off. Measured on polly's 44 targets: 1,848 of 4,894 mutants (38 %) fail to type-check, among them 323 of 974 survivors; the score it reports is lower (78.6 % against 80.1 %) because 1,489 of the kills were free |
| Run | One `bun test --bail` per mutant. `engine/preload.ts` swaps the target's text in a `Bun.plugin` `onLoad` — no sandbox copy |
| Isolate | Each test process runs in a fresh scratch cwd that carries the project's `tsconfig.json` (by `extends`) and `bunfig.toml` (preloads made absolute). A target whose tests pass only in the project dir (a fixture read through `process.cwd()`) runs in-tree, and the run says so. `--in-tree` turns this off |
| Matrix | `--mode matrix`: no `--bail`, a junit report per run, and every failing test in `killedBy`, so the redundancy sections turn on. A covering file that the baseline reported and a mutant run did not (it threw while loading) is named as `<file>#(file produced no results)@0`. A green baseline with no junit test case fails the target |
| Cache | `.polly/mutate/cache/` (it ignores itself in git). The key covers the generated mutants, every file the covering tests import, each mutant's selection, the preloads, tsconfig, bunfig, bun.lock, the mode, the type filter's on/off and Bun's version. The coverage pass has its own entry, keyed on every file the import graph holds. `--no-cache` reruns |
| Guard | `git status` snapshots before the run, after the baselines and after the mutants. Each path a mutant run adds to the worktree prints as a warning; nothing is deleted |
| Contracts | Every test process runs with `POLLY_CONTRACTS` set (default `all`), so a false `requires`/`ensures` from `@fairfox/polly/verify` throws a `ContractViolation` instead of being a no-op. See "Contracts as oracles" below |

```sh
polly mutate run                          # every target in the config
polly mutate run --files src/a.ts         # one target (globs, a.ts:10-20 ranges)
polly mutate run --since main             # only targets changed since a ref
polly mutate run --concurrency 10
polly mutate run --mode matrix            # every killer recorded
polly mutate verify --run                 # matrix pass, then the kill-matrix contract
polly mutate run --in-tree                # test processes run in the project dir
polly mutate run --coverage static        # no coverage pass: import-graph selection
polly mutate run --contracts ensures      # enforce postconditions only; off restores the no-ops
```

### Contracts as oracles

`requires(cond, msg)` and `ensures(cond, msg)` are runtime no-ops: the caller
evaluates `cond`, the primitive discards it, and only `polly verify` reads
the call. Every one of them is still an assertion the author wrote, placed in
the handler it describes. Under `POLLY_CONTRACTS` a false condition throws a
`ContractViolation` whose message starts with a marker
(`[polly-contract ensures /abs/handlers.ts:50] the author's message`), and the
engine sets that variable on every test process it starts — baseline,
coverage pass, mutant runs, both runner kinds — so each contract kills the
mutants that falsify it, in every test that drives its handler, whether or not
the test asserts on the outcome.

| Setting | Effect |
|---|---|
| `contracts: "all"` / `--contracts all` (default) | `requires` and `ensures` throw when false |
| `"ensures"` | postconditions throw; preconditions stay inert |
| `"off"` | the primitives are no-ops, as outside the engine |

The message bus turns a handler's throw into `{ success: false }`, so a
violation can pass unseen by the test that caused it. The primitives therefore
record each violation on `globalThis` before throwing, and the harness drains
the list: the engine preload fails the test in a global `afterEach` (a
violation during module load or `beforeAll` belongs to no test and is
logged), and `polly bdd run` fails the step. The preload also keeps the
target's line count when a mutant drops lines (an emptied block is followed by
a comment holding them), so the site a violation names is the source line.

What the run reports, in matrix mode:

- **`killedByContract`** on a mutant: the contract ids
  (`<file>:<line>`) the killing tests' failures named. **`contractOnly`**
  when every killer failed that way — no assertion caught the mutant, a
  contract did.
- **`CONTRACTS`** section of the report: contract-only kills; kills per
  contract; **contracts without teeth** — a site whose handler had mutants
  run and that never fired, the semantic twin of the static
  `no-tautology-ensures` check; and sites whose handler no mutant exercised.
- **`TEST VIOLATES CONTRACT`**: the unmutated code failed a contract under
  one of its own tests — a test drives a handler outside its declared
  precondition, or a handler breaks its own postcondition. The run stops
  with exit 1, names the test and the site, and that target's mutants are
  `RuntimeError`. This is deterministic, so the baseline is not retried.
  `--contracts ensures` leaves `requires` inert; `--contracts off` restores
  the no-ops. A silent fallback would make off/on kill counts incomparable.

Limits: fast mode (`--bail`) has no per-test results, so kills are not
attributed; the command runner has none either, so only the aggregate kill
count moves (compare a `--contracts off` run) and a red command is rerun once
with contracts off to tell a contract violation from any other failure. The
report and cache key carry the mode, so `off` and `all` never share results.

Proof surface: `scripts/e2e-mutate.ts` (`checkContracts`: the built package's
primitives, a swallowed `ensures`, off → Survived, all → Killed and attributed)
and `scripts/e2e-mutate-contracts.ts` (examples/todo-list through the BDD
command runner, killed count off against all).

The **command runner** (`runner: { kind: "command", argv }`) runs the argv once
per mutant in the config's directory; a non-zero exit kills the mutant. The
injection preload reaches every Bun process the command starts through
`BUN_OPTIONS`, so `bun run bdd` → `polly bdd run` sees the mutant. It selects
no tests, runs no coverage pass, runs fast mode only, is never cached (no import graph bounds what the
command reads), and a timeout kills the command's whole process group.

The contract between the engine and a command is two environment variables,
set for each mutant run and unset for the baseline:

| Variable | Value |
|---|---|
| `POLLY_MUTATE_FILE` | Absolute, symlink-resolved path of the target |
| `POLLY_MUTATE_SPAN` | JSON `{ "start", "end", "replacement" }`: replace characters `[start, end)` of the file's text with `replacement` |

A command that loads the target some other way than a Bun import must apply
the span itself. For a bundle there is a plugin:

```ts
import { pollyMutatePlugin } from "@fairfox/polly/mutate";

await Bun.build({ entrypoints: ["src/page.ts"], outdir: "dist", plugins: [pollyMutatePlugin()] });
```

With either variable unset it does nothing, so the build can keep it on.
`scripts/e2e-mutate.ts` (`checkBundle`) runs a command that bundles a page
and runs it under Node: 5 of 5 mutants survive without the plugin, 5 of 5
are killed with it.

### Disable comments

Stryker's comment syntax is read as it is, so a migrated project keeps its
comments. `polly-mutate` is accepted in place of `Stryker`.

```ts
// Stryker disable next-line ObjectLiteral: a data table
export const IMAGES = { … };

// Stryker disable ArrowFunction,BlockStatement: no route reads it yet
…
// Stryker restore ArrowFunction,BlockStatement

/* polly-mutate disable next-line all */
```

| Rule | Behaviour |
|---|---|
| `next-line` | Covers the line after the comment |
| No `next-line` | Covers every later line until a `restore` names the mutator |
| Mutator list | Comma-separated, any case; `all` names every mutator |
| Covered | The mutant's span starts on a covered line (Stryker's node-start rule) |
| Result | `Ignored`; `statusReason` is the text after the colon, else `Disabled by the comment on line N` |
| Verify callsite | Keeps its polly#143 reason; the comment is not counted as covering it |

`run` prints a warning for each comment that does nothing:

- `covers no mutant` — nothing on the covered lines mutates, or only verify callsites do;
- `covers only CompileError mutants` — the parse check or the type filter drops them anyway;
- `names no mutator: <name>` — a misspelt mutator matches nothing.

The type filter checks disabled mutants too, so that it can tell the last
case: a disabled mutant the tsconfig rejects is `CompileError`, not `Ignored`.

Operators are Stryker's 16 mutators, with Stryker's names and the rules of
`@stryker-mutator/instrumenter` 9.6.1, so a report reads the same from either
engine: ArithmeticOperator, ArrayDeclaration, ArrowFunction,
AssignmentOperator, BlockStatement, BooleanLiteral, ConditionalExpression,
EqualityOperator, LogicalOperator, MethodExpression, ObjectLiteral,
OptionalChaining, Regex (weapon-regex 1.3.6, level 1, the version Stryker
resolves), StringLiteral, UnaryOperator, UpdateOperator. Like Stryker, it
skips type-only syntax, imports, decorators and `declare` statements.

Intended differences from Stryker:

| Where | Stryker | This engine | Why |
|---|---|---|---|
| `expr as T` | Skips the whole subtree, `expr` included | Mutates `expr` | `expr` runs; skipping it hides mutants |
| `a ?? b` → `&&` | Babel regenerates the code | The result is parenthesised in the source span | `a ?? b ?? c` does not parse otherwise |
| Verify primitives | Mutated unless the polly ignorer is configured | `Ignored` by default (`ignoreVerifyCallsites`) | polly#143 |
| Mutant text | Babel's generated code | The original source with one span swapped | Comments and formatting stay byte-identical |
| Disabled mutant the tsconfig rejects | `Ignored` | `CompileError`, and the comment is reported unused | The comment is not needed; the warning says so |

The last row means a parity check must compare replacements after
normalising quotes and whitespace.

Current limits:

- **Fast mode has no killers.** `--bail` stops at the first failing test, so
  `killedBy` is empty and the redundancy sections stay off; use `--mode matrix`.
- **A Timeout has no killers.** The process is killed before Bun writes its
  junit report. Without `--bail` more mutants time out (179 vs 41 on polly's 44
  targets), so a test whose only kills are Timeouts can look subsumed.
- **The command runner's preload reaches Bun processes only.** A command that
  runs the target under Node, or bundles it, never loads the preload, so every
  mutant survives. A `Bun.build` takes `pollyMutatePlugin()`; anything else
  must apply `POLLY_MUTATE_FILE` / `POLLY_MUTATE_SPAN` itself.
- **Per-test selection drops kills that need another test's state.** A mutant
  runs only the tests that ran its code. A test that fails only through state an
  earlier test left behind (a lazy cache filled once) is not selected. On polly's
  44 targets this lost 0 kills against static selection (2026-10-20).
- **Module top-level code runs once per process.** Bun shares one module registry
  across the test files of a process, so a top-level hit lands in whichever file
  loaded the module first. Such a mutant runs, whole, every file that imports the
  target or hit any of its probes.
- **Concurrent tests** (`test.concurrent`, `--concurrent`), retries and
  `--rerun-each` break the ordinal match between hooks and junit cases. That file
  falls back to whole-file selection.
- **`--coverage static`** cannot see reach that no import names (`mock.module`, a
  computed `import()`, a global set by another file); the coverage pass sees it,
  because it runs every test file.
- A file that a bunfig `[test].preload` imports is loaded before the mutant
  plugin registers, so it cannot be mutated.
- **A contract violated outside any test** (module load, `beforeAll`) is
  logged, not attributed: no test owns it.

Proof surface: `scripts/e2e-mutate.ts` (cold-start project, source and built CLI,
`--since`, `init` then `run`, a Stryker-only project before and after `migrate
--write`); the engine's own tests are the `tools.mutate` tier case.

### Decisions log

Signals are derived and regenerable; **decisions** about them are not, and live
in `.polly/test-debt/decisions.jsonl` (committed, mergeable, append-only,
last-write-wins per file; override with `--decisions <path>`). Record one with:

```sh
polly mutate decisions decide <test-file> <keep|prune|rewrite|investigate> "<rationale>"
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

Matrix mode runs every covering test for each mutant, with no `--bail`, and
reads Bun's junit output (`--reporter=junit`, parsed in `engine/junit.ts`):
every failing test is a killer, keyed `<relfile>#<name>@<line>`, and the same
function builds the `testFiles[].tests[]` ids, so every `killedBy` id
resolves. A test file that fails to load leaves no junit element; it is
recorded as a `(file produced no results)` stand-in killer.

This rests on Bun's junit format. A Bun upgrade that changes it, or a `--bail`
that creeps back into matrix runs, collapses the matrix to one killer per
mutant. `polly mutate verify` is the guard — run it after any Bun bump.

**NoCoverage vs Survived.** With dynamic coverage (the default) the split is per
mutant: a mutant whose code no test ran is NoCoverage (a true gap); one that ran
and was not detected is Survived (theatre). `coveredBy` names the tests that ran
it. Under `--coverage static` the split is per file: a target no test file
imports is NoCoverage, and every undetected mutant in a reached file is Survived.

## Comparing with Stryker

Stryker is not a dependency. `scripts/mutate-parity.ts` compares the two on the
current tree, using a pinned Stryker held outside the workspace
(`scripts/mutate-parity/stryker/`, installed into `~/.cache/polly` on first use):

```sh
bun packages/polly/scripts/mutate-parity.ts                    # the four reference targets
bun packages/polly/scripts/mutate-parity.ts --files a.ts,b.tsx # any targets
```

It checks mutant match rate, lost kills, score gap and wall time.
`scripts/mutate-parity.results.md` holds the committed run (2026-10-20: 99.3 %
matched, 0 lost kills, score gap 0.07, 39.5× faster).

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

- **Timeouts.** Mutating async/retry code produces hangs. The engine's budget is
  the target's baseline × `timeout.factor` + `timeout.extraMs` (default ×2 + 3 s),
  so a hang costs seconds, not Stryker's former 90 s. A timeout scores as detected.

- **Tests run from the repo root.** `polly.mutate.ts` sits at the monorepo root,
  so test globs are repo-root relative and each test process gets a scratch cwd
  whose `tsconfig.json` extends the root one (Bun reads JSX settings from the cwd
  tsconfig; without it polly-ui `.tsx` would compile for react). Polly-ui test
  subsets need `tests/setup.ts` (the CSS-module shim) as a preload; the config
  lists it.
