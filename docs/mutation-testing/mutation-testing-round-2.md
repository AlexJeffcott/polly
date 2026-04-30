# Mutation Testing — Round 2

Targets: blob storage, mesh-state, peer-state, message-bus.

| #  | File                  | Category                          | Result    |
|----|-----------------------|-----------------------------------|-----------|
| 6  | blob-store-impl.ts    | Removed integrity check           | caught    |
| 7  | mesh-state.ts         | Lost domain separation in hash    | SURVIVED  |
| 8  | peer-state.ts         | Inverted validation               | caught    |
| 9  | message-bus.ts        | Wrong success/failure signal      | SURVIVED  |
| 10 | message-bus.ts        | Off-by-one in branch threshold    | caught    |

2 survivors, 3 caught.

---

## Mutation 6 — blob-store-impl.ts: drop hash check on `put`

**Location:** `src/shared/lib/blob-store-impl.ts:312`

**Change:** removed `if (hash !== ref.hash) throw …` so `put()` accepts
bytes that don't match the supplied `BlobRef`. The store would happily
cache mismatched bytes under the wrong content-address — every later
fetcher would then hash-mismatch on download.

**Result:** caught. 1 failure: `createBlobStore — core > put rejects
when hash does not match`.

**Test quality:** the canary test does its job. Single-line, single
expect, but the behaviour it pins is exactly the integrity invariant.

---

## Mutation 7 — mesh-state.ts: drop domain separation in `deriveDocumentId`

**Location:** `src/shared/lib/mesh-state.ts:120`

**Change:** swapped the input to `nacl.hash` from
`${DOC_ID_DOMAIN}:${key}` to just `key`. The DocumentId derived for any
given application key is now a different deterministic id, but still
deterministic per process — one device's view stays consistent with
itself, and a fresh process re-derives the same (mutated) id from the
same key.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** the test suite never asserts on the *value* of the
derived DocumentId, only that two derivations from the same key
agree. Domain separation is a property that only matters across
subsystems (a future Polly subsystem reusing `nacl.hash(key)` would
collide with mesh-state's documents). No test reaches across that
boundary.

**Severity:** medium-low at present, latent-high. The mutation is
silent today; it becomes a footgun the moment a second subsystem hashes
keys for any purpose (signing salts, blob ids, anything).

**Test gap:** no value-level assertion on derived ids, no
cross-subsystem collision test. A single test of the form
`expect(deriveDocumentId("foo")).toBe("known-hex")` would have caught
this, and a second test asserting `deriveDocumentId("foo")` differs
from any other-subsystem-derived id would catch the latent class.

---

## Mutation 8 — peer-state.ts: invert `validateSignOption`

**Location:** `src/shared/lib/peer-state.ts:127`

**Change:** flipped the `signingEnabledRepos.has(repo)` check so the
"sign: true" option is rejected when signing IS enabled and accepted
when it isn't. Exactly backwards.

**Result:** caught. 3 failures, all in the `$peerState — sign option`
suite.

**Test quality:** good, and notable for what it asserts: both
directions of the predicate (the "throws when sign true without
signing-enabled Repo" test AND the "accepts sign true when the Repo
was configured with signing" test). This is the pattern the rest of
the suite should aspire to — when checking a binary discriminator,
test both buckets.

---

## Mutation 9 — message-bus.ts: missing handler reports `success: true`

**Location:** `src/shared/lib/message-bus.ts:575`

**Change:** changed `return { success: false, error: "No handler" }`
to `return { success: true, error: "No handler" }`. Any caller that
sends a request whose payload type has no registered handler now
receives a successful response rather than a failure. The error string
is still attached but `success: true` is the discriminant most callers
check.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** there are tests that assert "console.warn was
called" for unknown message types (the warn line one above the return
statement) but none that asserts on the *response* shape of an
unhandled message. The only place the missing-handler return value
matters is in the round-trip; the unit tests for message-bus stop at
the warn call.

**Severity:** medium. In production a caller that sends a request to a
context that doesn't have the handler registered (e.g. due to a typo
or a load order issue) gets back a fake success and proceeds as
though the work was done. This is the canonical "silent success"
failure mode — the worst kind to debug.

**Test gap:** symmetric to Round-1 M3 — the unit suite asserts on
side-effects (the warn call) instead of on the actual return value
that downstream code consumes. Pattern: "assert on the value the next
caller will see, not just on the side-effect that happens to fire on
the way there."

---

## Mutation 10 — message-bus.ts: `length > 1` → `length >= 1`

**Location:** `src/shared/lib/message-bus.ts:579`

**Change:** flipped the branch so single-target messages take the
multi-target path. The multi-target path doesn't `sendResponse`, so
single-target requests never get a reply and the caller's pending
request waits for the timeout.

**Result:** caught. 59 failures + 10 errors. Runtime: 297 s (vs.
12 s baseline) because the timeouts are 5 s each and several tests
serialised them.

**Test quality:** the integration tests do round-trip and time out;
the unit tests fail fast with assertion mismatches. The catch is
real but expensive — a single bug spreads across 69 tests because the
broken codepath is on the request/response highway. A faster signal
would be a unit test that asserts "single-target request to a known
handler resolves with a response", which would fail in 5 s rather than
five minutes.

---

## Round-2 Findings

**Two survivors, both share the same root cause as Round 1:** tests
assert on side-effects rather than on the value the next caller
consumes.

- M9 (handler returns wrong success bool): the warning that fires
  alongside the return is asserted; the return itself is not.
- M7 (domain separation lost): determinism is asserted (same key →
  same id within a run); the actual value of the id, and its
  cross-subsystem distinctness, is not.

**Caught mutations had a pre-existing dedicated test.** M6 (blob hash
mismatch), M8 (peer-state sign option), M10 (response routing) all
have a test whose name is essentially a transliteration of the
invariant being violated. Pattern: when a behaviour has a
single-sentence specification, write a test whose title is that
sentence and whose body asserts the value, not a side-effect.

**Cost-of-detection signal.** M10 took 297 s to surface — 25× the
baseline runtime — because the failure mode was "request never
resolves" and the test infrastructure waits 5 s per timeout. This is
a useful weak signal for "does this codepath have a tight unit test or
only a slow integration test?" — if mutation tests on a module
balloon runtime by an order of magnitude, the unit coverage on that
module is doing nothing fast.
