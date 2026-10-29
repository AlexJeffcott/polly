# Bun safety checker (spike)

**Status:** steps 2–5 done 2026-10-29. The general checker (steps 3a and 3b
below) moved out of this directory to `tools/verify/src/checker/` and ships
as `polly verify --engine bun`; its CLI for the scripts here is
`tools/verify/src/checker/cli.ts`. `parity.ts` became the parity gate
`scripts/e2e-verify-bun-parity.ts` (tier case `verify.bun-parity`), and
`tlc-counts.json` became `scripts/e2e-verify-bun-parity.counts.json`. What
stays here is the history: the hand-written minimal checker (`check.ts`), the
bench scripts and their logs. `scripts/spikes` is excluded from typecheck, biome and semgrep
(`packages/polly/tsconfig.json`, `biome.json`, `scripts/check.ts`), not from
the casts gate.

An explicit-state breadth-first checker for the TLA+ spec that `polly verify`
generates for `examples/minimal`. It checks safety only (invariants under the
CONSTRAINT), in one thread. It gives the same generated, distinct and depth
counts as TLC.

## Why continue

| Reading | Value |
|---|---|
| Agreement with TLC | Exact generated / distinct / depth on 4 configs, states up to 88 bits |
| Speed | 11–19× TLC `-workers auto`; 23–30× TLC `-workers 1` |
| Memory | 1/10 to 2/5 of TLC's container peak |
| Docker / Java | Not needed |
| Defects found while building it | Handlers no run ever took (minimal, full-featured, mesh-recovery-pair) → handler coverage, 900be3d; `NoRoutingLoops` false at `MaxMessages >= 3` → 22fa537; mesh-recovery-pair chain cut at `maxInFlight: 2` → da12d18 |

## Measurements

Same machine, safety only. TLC time is `real` from `tlc.sh` (includes about 3 s
of container start). Bun time is BFS wall time. Raw runs:
`bench-2026-10-27.log`.

| Spec | Generated | Distinct | Depth | Max bits | TLC w1 | TLC auto | Bun | TLC auto peak | Bun RSS |
|---|---|---|---|---|---|---|---|---|---|
| minimal, 2026-10-28 (one payload record) | 8,940,937 | 2,005,064 | 14 | 70 | — | 23 s | 1.1–1.2 s | 1.88 GB | 0.18 GB |
| minimal, 2026-10-27 (8 payload records) | 101,415,368 | 16,040,512 | 14 | 73 | 407–415 s | 146–169 s | 13.5–13.7 s | 3.74 GB | 1.01–1.05 GB |
| `w_bp3t1`, 2026-10-27 | 79,412,392 | 13,749,504 | 18 | 83 | 245–252 s | 120 s | 10.7–10.9 s | 2.36–2.44 GB | 1.00 GB |
| `w_b4`, 2026-10-27 | 35,201,656 | 7,146,992 | 22 | 88 | 121–122 s | 59–60 s | 4.8–4.9 s | 1.93–1.96 GB | 0.60–0.65 GB |

`w_bp3t1` and `w_b4` are variants of the minimal spec with wider states; their
spec directories were not kept.

## Run

```sh
# 1. Generate the spec: writes examples/minimal/specs/tla/generated
cd examples/minimal && bunx polly verify
# 2. TLC and Bun on the same spec, safety only; exit 0 when all three counts match
packages/polly/scripts/spikes/bun-checker/compare.sh
```

| File | Purpose |
|---|---|
| `check.ts` | The checker. `--spec DIR`, `--bug loops` (an invariant that fails), `--bug probe`, `--fp-only` (TLC-style fingerprint-only set), `--dump FILE` |
| `compare.sh` | TLC vs Bun on minimal's current spec; prints MATCH or DIFFER |
| `tlc.sh` | TLC as polly's runner starts it, plus the container's `memory.peak` |
| `bench.sh` | 3 × TLC w1, 3 × TLC auto, 3 × Bun per spec directory |

## Limits

- The actions are written by hand for minimal's two handlers (`ACTIVATE`,
  `PING`) and the fixed MessageRouter. Another spec needs new code.
- Known invariants only: `TypeOK`, `NoRoutingLoops`, `UserStateTypeInvariant`.
  Any other name in the cfg is an error.
- No liveness, no temporal properties (`EnsuresAfter_*`), no counterexample in
  TLC's trace format.
- Constants and set sizes are read from the `.cfg` / `.tla` with regexes.

## TLC rules it must keep

- CONSTRAINT: a successor outside the constraint counts as generated, not as
  distinct; its invariants are checked; it is not expanded.
- `PayloadType` is either the record set or one record
  (`{CHOOSE p \in [...] : TRUE}`, since 922db6b).
- `NoRoutingLoops == routingDepth <= Len(messages)` (since 22fa537).

## General checker (step 3a, 2026-10-28)

`tlacheck.ts` with `tla/` (lexer, parser, values, evaluator) reads the
generated `.tla` and `.cfg` as TLC does. Nothing in it is written for one
example. A construct it does not support stops the run with exit 3.
`parity.ts` (now `scripts/e2e-verify-bun-parity.ts`) runs it and TLC
(`-workers 1`) on every generated spec set:

| Set | Generated / distinct / depth | TLC w1 | tlacheck | Verdict |
|---|---|---|---|---|
| full-featured | 1,803,067 / 234,398 / 5 | 16.7 s | 62.7 s | MATCH |
| mesh-recovery-pair | 8,335,640 / 2,322,383 / 20 | 58.2 s | 174.0 s | MATCH |
| minimal | 8,940,937 / 2,005,064 / 14 | 47.2 s | 180.3 s | MATCH |
| todo-list/auth | 5,433,816 / 289,440 / 5 | 17.7 s | 74.4 s | MATCH |
| todo-list/preferences | 443,544 / 24,816 / 5 | 2.0 s | 4.0 s | MATCH |
| todo-list/todos | 6,407,144 / 495,616 / 5 | 32.3 s | 135.6 s | MATCH |
| elysia-todo-app/server, team-task-manager/client | TLC does not end | — | — | EXCLUDED |

TLC rules found while building it:

| Rule | Evidence |
|---|---|
| With `-workers auto`, TLC's reported depth is not deterministic | mesh-recovery-pair: 20 with 1 worker, 21 and 22 on two `auto` runs |
| `TLCGet("level")` in a constraint reads the level of the state being expanded | todo-list sets: `TLCGet("level") <= 4` gives depth 5 |

Speed: the interpreter is 2–4× slower than TLC with one worker, and minimal
peaks at 4.94 GiB. Its profile has no single hot spot (value building and
keys 29 %, tree walk 26 %). Step 3b compiles instead of interpreting.

## Compiled engine (step 3b, 2026-10-28)

`tlacheck.ts` now compiles the spec to JavaScript (`tla/compile.ts`) over
interned values (`tla/runtime.ts`); `--engine interp` keeps the 3a
interpreter. Stop rule, agreed 2026-10-28: at least 3x TLC `-workers auto` on
full-featured. Result: PASSED, 3.1x worst case, 3.3x median.

`bench-3b.sh`, TLC and Bun runs in turn, 3 rounds (`bench-3b-2026-10-28.log`).
Wall time is `real` for both; TLC includes about 3 s of container and JVM
start. Memory: container `memory.peak` for TLC, max RSS for Bun. Counts were
equal in every run.

| Set | TLC auto | Bun | Ratio | TLC memory | Bun memory |
|---|---|---|---|---|---|
| full-featured | 3.74–6.25 s | 1.14–1.20 s | 3.1–3.3x | 1.40 GB | 0.36 GB |
| minimal | 16.7–18.9 s | 2.42–2.45 s | 6.9–7.8x | 1.74 GB | 0.36 GB |
| mesh-recovery-pair | 20.6–21.0 s | 4.62–4.74 s | 4.4–4.5x | 1.60 GB | 0.88 GB |
| todo-list/auth | 4.80–5.15 s | 1.80–1.90 s | 2.5–2.9x | 1.36 GB | 0.37 GB |
| todo-list/preferences | 1.40–1.45 s | 0.16–0.18 s | 8.2–9.1x | 0.57 GB | 0.12 GB |
| todo-list/todos | 7.27–7.42 s | 2.82–2.86 s | 2.5–2.6x | 1.55 GB | 0.40 GB |

How the engine gets its speed, in order of effect on full-featured (62.7 s
interpreted):

| Change | full-featured |
|---|---|
| Interned values (one ID per value; a state is an Int32Array; exact visited set) and actions compiled to for/if code, constants folded at compile time | 2.32 s |
| Loops over `DOMAIN f` and `1..Len(f)` bind `f[x]` once; grouped EXCEPT; lazy assignments inside ENABLED; repeated guards dropped; `[x \in DOMAIN f \ T |-> f[x]]` as one operation; states already checked are not checked again | 1.94 s |
| Pure guards hoisted out of `\E` loops (`SendMessage` ran 378 combinations before its guards) | 1.56 s |
| Constraint and invariant conjuncts cached by the value IDs they read | 1.42 s |
| No typed-array views in the value store | 1.23 s |

Tests that the checker can fail: an invariant that a normal run breaks, and
one that only out-of-constraint states break, are reported with exit 12
(TLC reports both). `SYMMETRY` in the cfg gives exit 3.

## Plan to continue

1. DONE as 3a and 3b: compile the generated `.tla`, so TLC and the checker
   read the same file (decided 2026-10-28). 3b passed its stop rule.
2. DONE 2026-10-29: packed visited set (`tools/verify/src/checker/state-store.ts`).
   Each variable gets its own dense numbering of the value IDs it takes, and
   a state is those numbers packed into 32-bit words, each field as wide as
   its dictionary needs (widened by doubling; stores re-encode). Bounds come
   from the values seen, not from the config, so no varint is needed; the
   set stays exact (word compare), so no fingerprint. 2 words per state on
   every parity set, against 8. A full GC every 2^20 expanded states: the
   compiled actions' closures were 4.8 GiB of uncollected garbage on
   webrtc-p2p-chat/client, because JSC's trigger scales with the stores'
   typed arrays (15,788 live objects, so the collection is cheap).

   | Reading | Before | After |
   |---|---|---|
   | webrtc-p2p-chat/client (123,836,552 states), peak RSS | 13.0–14.1 GB | 6.95 GB; 4.65 GB with the closures lifted |
   | same, wall | 222–236 s | 177 s; 180 s with the closures lifted |
   | minimal, peak RSS / wall | 0.41–0.42 GB / 2.57–2.59 s | 0.28–0.30 GB / 2.53–2.58 s |
   | mesh-recovery-pair | 0.94–0.95 GB / 4.76–4.80 s | 0.77–0.81 GB / 4.76–4.78 s |
   | full-featured | 0.40–0.41 GB / 1.29–1.30 s | 0.41–0.43 GB / 1.32–1.33 s |

   Stop rule (set 2026-10-29): webrtc peak at most 60 % of before (53 %),
   small sets at most 10 % slower (+3 % worst). Tried and dropped: rows in
   fixed chunks and a 256-part hash index (5.25 GB peak, 10–15 % slower);
   a GC after each large array is replaced (11.6 GB, worse).

   Then (2026-10-29): `tla/compile.ts` `lift` turns each closure called at
   once (8 sites: set builders, CHOOSE, EXCEPT, Cardinality, quantifiers,
   ENABLED) into a call to a function at module level, its free variables
   as parameters. 0 closures left on the 6 parity sets. webrtc peak 6.95 →
   4.65 GB; the small sets 0–9 % faster. The periodic GC stays: without it
   webrtc still peaks at 7.18 GB.
3. DONE 2026-10-29: parity gate `scripts/e2e-verify-bun-parity.ts`, tier
   case `verify.bun-parity` (Docker). Cold copies of the examples, verified
   with `--engine bun`; each generated set compared with TLC `-workers 1`.
   TLC runs only for a set whose hash is not in the committed count file.
   The repo has no hosted CI; the verify tier is the gate.
4. DONE 2026-10-28: `polly verify --engine bun` (or `verification.engine`).
   Safety only; PROPERTIES listed as not checked (`--strict` fails on them);
   a spec it cannot read falls back to TLC (`--strict` fails). Handler
   coverage from a `cover` node put before each `Handle*` action's last
   conjunct. Proof: `scripts/e2e-verify-bun-engine.ts`. The interpreter's
   action enumeration (3a) was removed; the compiler uses the evaluator for
   constant expressions only.
5. DONE with step 4: a violation gives a shortest trace (parent index per
   stored state), `State N:` / `/\ var = value` lines as TLC prints them.
