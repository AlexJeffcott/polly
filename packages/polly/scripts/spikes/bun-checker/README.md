# Bun safety checker (spike, parked)

**Status:** parked 2026-10-28, with the intention to continue. Not shipped. No
tier runs it. `scripts/spikes` is excluded from typecheck, biome and semgrep
(`packages/polly/tsconfig.json`, `biome.json`, `scripts/check.ts`), because
this code is reference only. The generator in the plan below replaces it.

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

## Plan to continue

1. Emit the checker from polly's internal model, not from the `.tla`.
   MessageRouter is a fixed template; only handler actions (requires, writes,
   ensures) and the state schema differ between models.
2. Encoding: the variable-length bit string in `check.ts` (bounds from the
   config, varint for unbounded naturals, 64-bit fingerprint with exact word
   compare).
3. Parity gate: run TLC and the generated checker on every example in CI;
   fail on any difference in generated / distinct / depth.
4. Add as a `polly verify` option for safety runs. TLC stays the reference and
   runs liveness and temporal properties.
5. Counterexample traces in a form the existing TLC trace reader accepts.
