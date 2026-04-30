# Mutation Testing — Round 4

Targets: state.ts (Lamport-clock + deepEqual), resource.ts (skipped —
no obvious low-risk mutation that wasn't already redundant with state),
guards.ts, blob-transfer.ts, log-store.ts.

| #  | File                | Category                          | Result    |
|----|---------------------|-----------------------------------|-----------|
| 16 | state.ts            | Weakened Lamport monotonicity     | SURVIVED  |
| 17 | state.ts            | deepEqual mismatched-key tolerated| SURVIVED  |
| 18 | blob-transfer.ts    | Removed missing-chunk throw       | caught    |
| 19 | log-store.ts        | Wrong end of buffer evicted       | caught    |
| 20 | guards.ts           | isRecord accepts arrays           | SURVIVED  |

3 survivors, 2 caught. The worst round so far in coverage terms,
and the survivors are all foundational primitives that everything
else relies on.

---

## Mutation 16 — state.ts: Lamport `>` → `>=`

**Location:** `src/shared/lib/state.ts:351`

**Change:** weakened the strict-greater check so that incoming sync
messages with a clock equal to the local clock are also applied. The
"only causally newer updates" invariant becomes "causally newer or
equal". The line above (`entry.clock = Math.max(...)`) is unchanged so
the clock still moves correctly; only the value-update gate is loose.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** the existing Lamport-clock tests construct
scenarios with clearly-ordered clocks (1 then 2, or 5 then 3) and
assert the value either updates or does not. None construct the
*equal-clock* scenario where two devices independently mint the same
clock value — the case where strict-vs-loose comparison actually
discriminates.

**Severity:** medium. Equal Lamport clocks across devices are not
the common case but they're not vanishing either; they happen exactly
when two devices write concurrently from offline storage with their
local clocks at the same value. The strict-greater rule prevents one
device's view from oscillating between values; the loose rule lets
late-arriving messages clobber identical-clock writes.

**Test gap:** boundary case again. Same shape as Round 1 M3 / Round 3
M14: production rule is "strictly greater", existing tests assert on
"clearly greater" and "clearly less", the equality boundary is
untested.

---

## Mutation 17 — state.ts: `deepEqual` continues past missing key

**Location:** `src/shared/lib/state.ts:196`

**Change:** in `deepEqual`, switched the missing-key branch from
`return false` to `continue`. Two objects with the same key count but
different sets of keys (e.g. `{a:1, b:2}` vs `{a:1, c:3}`) are now
classified as equal as long as the overlapping keys match.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** `deepEqual` is used as a "no-op short-circuit" in
sync ingestion (line 362) and in the `$resource` source-tracker. Both
call sites pass shapes the application authored on both sides — the
pathological case (same key count, different key sets) doesn't arise
naturally in the existing tests. The function has no dedicated test;
its correctness is assumed.

**Severity:** medium-high. `deepEqual` is the primitive the entire
state-redundancy guard rests on. A wrong "equal" verdict drops a
legitimate update silently. Hard to debug — the value just doesn't
update and there's no error.

**Test gap:** load-bearing primitive with no dedicated test file.
`access.ts` has a test for every compositor; `deepEqual` has no tests
at all.

---

## Mutation 18 — blob-transfer.ts: drop missing-chunk throw

**Location:** `src/shared/lib/blob-transfer.ts:78`

**Change:** replaced the `throw new Error("missing chunk")` with
`continue`, so reassembly silently skips missing chunks. The second
loop (line 86) then dereferences `chunk.length` on undefined and
crashes with a TypeError, which still surfaces to the caller — the
test still sees a thrown exception, just with a different message.

**Result:** caught. 1 failure: `reassembleChunks > throws when a
chunk is missing`. The test asserts on the existence of a throw, not
on its specific message, so the TypeError satisfies it.

**Test quality:** good *for this mutation*. A more cunning mutation
that also removed the dereference would let reassembly silently
produce a truncated blob. The test passes today but doesn't fully
specify the contract.

---

## Mutation 19 — log-store.ts: `pop()` instead of `shift()`

**Location:** `src/background/log-store.ts:42`

**Change:** ring-buffer eviction now drops the most recent entry
instead of the oldest. After every overflow the buffer is stuck at
`maxLogs` entries with the latest one repeatedly evicted.

**Result:** caught. 1 failure: `LogStore - implements circular buffer
(removes oldest)`.

**Test quality:** the test name is exactly the contract being
violated; the assertion checks the actual evicted entry, not just the
length. Textbook coverage of this kind of bug.

---

## Mutation 20 — guards.ts: `isRecord` accepts arrays

**Location:** `src/shared/lib/guards.ts:35`

**Change:** dropped the `!Array.isArray(input)` clause. `isRecord([])`
now returns `true`, narrowing the array to `Record<string, unknown>`.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** `isRecord` has no tests at all. Searching the
test directory for "isRecord" returns zero hits. The function is used
in several places (notably the API-client and message-bus
deserialisation paths) but every call passes through into a key access
that happens to also be valid on arrays (`x["foo"]` on an array is
just `undefined`), so the behaviour difference is hidden until a
caller does something array-specific.

**Severity:** medium. The bug is dormant because all current callers
narrow further immediately. A future caller that assumes `isRecord`
already excluded arrays — exactly the contract its name promises —
would get a surprise.

**Test gap:** the file has no test at all. `guards.ts` is one of the
most-imported modules in the codebase, used at every external
boundary, and its two functions have no unit tests.

---

## Round-4 Findings

**Three survivors, all in primitives that other code trusts implicitly.**
This is the round where the test-gap pattern shifts. Rounds 1–3
showed missing-boundary and side-effect-vs-value gaps in modules
*with* dedicated tests. Round 4 shows a different gap: load-bearing
primitives that have no dedicated tests because they're "obvious".

- M16 (Lamport `>` boundary): no equal-clock test
- M17 (`deepEqual`): no test file at all
- M20 (`isRecord`): no test file at all, no usage tests either

The pattern: **a tiny utility that everything depends on is the
hardest thing to test, because the developers who write it know what
it does and don't think to write a test, and the developers who use
it trust the name.** Rounds 1–3 mutations were caught when the test
suite asserted on the contract; Round 4 mutations survived when the
contract was implicit.

**Caught mutations in Round 4 share a feature:** the contract
appears verbatim in the test name ("removes oldest", "throws when a
chunk is missing"). Tests written from the contract catch contract
mutations.

**Suggested concrete additions:**

1. A `state.test.ts` block for `deepEqual` with the canonical
   permutations: same-keys-different-values, different-keys-same-value-count,
   nested differences, primitives, null vs undefined, array vs object,
   circular references (graceful failure expected).

2. A `guards.test.ts` file for `isRecord` and `hasKeyInObject` covering
   arrays, null, primitives, objects with own properties, and (for
   `hasKeyInObject`) the prototype-chain exclusion.

3. An equal-clock case in the Lamport-clock state tests, asserting
   that an incoming message with the same clock as the local clock is
   *not* applied.
