# Mutation Testing — Round 1

Goal: deliberately introduce subtle bugs into polly's source, then run the
full test suite to discover which classes of bug pass undetected. The point
is not the bugs themselves — it is the gaps in the test harness that
surface when a mutation survives.

Method: for each mutation, apply it with `Edit`, run `bun run --cwd tests
test`, record the outcome, then revert. The unit suite runs in ~12 s and
is the immediate feedback loop. We sample example tests on the most
surprising survivors.

Baseline: 661 pass / 0 fail / 1360 expect() calls / ~12 s on this machine.

| # | File                | Category                     | Result    |
|---|---------------------|------------------------------|-----------|
| 1 | revocation.ts       | Dropped security cross-check | SURVIVED  |
| 2 | access.ts           | Logic-operator inversion     | caught    |
| 3 | message-router.ts   | Loop truncation              | SURVIVED  |
| 4 | crdt-state.ts       | Removed load-bearing guard   | SURVIVED  |
| 5 | signing.ts          | Security-primitive bypass    | caught    |

Three of five mutations passed every test. One of those — mutation 4 —
even has a regression test written specifically for it that did not fire.

---

## Mutation 1 — revocation.ts: drop issuer/sender cross-check

**Location:** `src/shared/lib/revocation.ts:339`

**Change:** removed the post-decode check that the payload's claimed
`issuerPeerId` matches the envelope's authenticated `senderId`. With the
check gone, a peer can sign an envelope as themselves but embed a payload
naming any other peer as the issuer. `decodeRevocation` now returns a
record whose claimed issuer was never authenticated.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** `tests/unit/revocation.test.ts` has 16 tests but none
that constructs a malformed payload-vs-envelope pairing. The test fixture
always builds the record and the envelope from the same issuer, so the
check is never the discriminator between pass and fail.

**Severity:** high. The cross-check is the only line preventing a forged
revocation that names an authority the attacker does not control as the
issuer. Combined with revocation-authority sets (which are checked
against `envelope.senderId`), the bug allows a non-authority peer to
issue revocations naming an authority — the authority check passes
because it inspects the envelope sender, but the resulting record
attributes the action to the impersonated peer, which is what
`applyRevocation` and audit code consume.

**Test gap:** the suite has no negative-construction test where the
record and envelope intentionally disagree.

---

## Mutation 2 — access.ts: `and()` returns `||`

**Location:** `src/shared/lib/access.ts:120`

**Change:** swapped `&&` for `||` inside the `and` compositor.

**Result:** caught. 2 failures:

- `compositors > and() accepts only when both predicates accept`
- `compositors > and() short-circuits on false`

**Why it was caught:** `access.test.ts` exercises the truth table. The
"short-circuits on false" test specifically constructs a predicate `b`
that throws if called and asserts `and(false, b)` does not call it —
under the OR mutation it does call `b`, so the throw bubbles up.

**Test quality:** this is what the rest of the suite should look like.
Asserts behaviour, not just outcomes; covers the boundary cases that
distinguish similar implementations.

---

## Mutation 3 — message-router.ts: only route first target

**Location:** `src/background/message-router.ts:174`

**Change:** replaced `for (const target of message.targets)` with
`for (const target of message.targets.slice(0, 1))`. Multi-target
routes now silently lose every target after the first. Single-target
routes are unaffected.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** every `targets:` literal across
`message-router.test.ts`, `message-router-logging.test.ts`,
`message-router-no-loops.test.ts` and `cross-context.test.ts` is a
single-element array. There is one test for `broadcastToAll`, but the
broadcast targets array passed in only contains a single context, so
the iteration body still runs exactly once.

**Severity:** medium-high. `broadcastToAll` is the only multi-target
caller in the public API and it is genuinely multi-target in production
(content + devtools + popup), so this mutation breaks broadcasts in
practice.

**Test gap:** the iteration logic in `routeMessage` is uncovered.
A single test of the form `targets: ["content", "popup"]` with both
ports connected would catch this and any future variant (skipped
target, duplicate target, ordering bug).

---

## Mutation 4 — crdt-state.ts: remove load-bearing equality check

**Location:** `src/shared/lib/crdt-state.ts:225`

**Change:** removed the `if (fieldEquals(doc[key], incoming)) continue;`
short-circuit inside `applyTopLevel`. The source comment on this line is
explicit that the check is "load-bearing, not an optimisation", with a
detailed explanation of how the missing skip causes a preact-signals
"Cycle detected" under bun timing.

**Result:** **SURVIVED.** 661 / 661 pass.

**Notable:** there *is* a regression test —
`crdt-state.test.ts:188` — titled "structurally-equal writes don't
cascade into a signal cycle", with a comment that says
"Pre-fix this threw 'Cycle detected' on the second write." It writes
ten value-equal objects in a tight loop. The test passed even with the
guard removed.

**Why the regression test didn't catch it:** the test uses an in-memory
`Repo` from `@automerge/automerge-repo`. The cycle the comment describes
is timing-dependent — the source comment itself notes "Browsers mask
this under typical interactive timing; a tight CLI boot reproduces it
every time." Whatever timing produces the cycle in the failing-CLI case
does not reproduce inside `bun test` with the in-memory repo, so the
test that exists to guard against the regression no longer exhibits it.

**Severity:** unknown. The guard is correct in production but the test
has drifted out of fidelity with the failure it was written to catch.
Either the production conditions changed, the dependency timing changed,
or the test was always sampling a non-failing path.

**Test gap:** a regression test that has lost contact with the failure
it was written to reproduce. The cycle-detection assertion needs to be
either (a) run against a live `@fairfox/polly` factory path under the
exact timing that originally failed, or (b) replaced with an assertion
on the lower-level invariant ("no Automerge ops are recorded for
value-equal writes") that does not depend on the cycle materialising.

This is the same class of failure described in
`~/projects/CLAUDE.md`'s "Green checks do not prove features work" note
— a regression test that runs the unit-level happy path while silently
no longer exercising the integration surface that originally broke.

---

## Mutation 5 — signing.ts: `verify()` always returns `true`

**Location:** `src/shared/lib/signing.ts:145`

**Change:** replaced the `nacl.sign.detached.verify(...)` call with
`return true`. Length checks remain so the function still rejects
misshapen inputs; only the cryptographic verification is short-circuited.

**Result:** caught. 7 failures across `signing.test.ts`,
`revocation.test.ts`, and the envelope tests:

- `sign and verify > a tampered payload fails verification`
- `sign and verify > a tampered signature fails verification`
- `sign and verify > a different public key fails verification`
- `signEnvelope and openEnvelope > openEnvelope throws if signed by a different key`
- `signEnvelope and openEnvelope > openEnvelope throws if the payload was tampered with`
- `encodeSignedEnvelope and decodeSignedEnvelope > decode throws on a truncated payload`
- `encodeRevocation and decodeRevocation > decodeRevocation throws on a tampered payload`

**Test quality:** good. The signing module has both positive (round-trip)
and negative (tampered, mismatched) tests, plus the negative tests
propagate naturally up to the consumers (envelope, revocation). A
single subverted line trips three layers of negative tests.

---

## Round-1 Findings

**Survivor pattern: missing negative tests for cross-fixture invariants.**

All three survivors broke an assertion that one part of a data structure
matches another part. None of the existing tests build the discordant
case:

- M1: payload's `issuerPeerId` ≠ envelope's `senderId`
- M3: `targets.length > 1`
- M4: a stale fixture that no longer reproduces its target failure

Where polly's tests are good — `access.ts`, `signing.ts` — they assert
on the boundary case that distinguishes correct from almost-correct
implementations: the "short-circuits on false" test, the "different
public key fails" test. Where the tests are bad, they only construct
the canonical happy-path shape (single-target routing, matching
issuer-and-sender, same-value writes that no longer cycle).

**The test harness's most reusable weakness is fixture monoculture.**
Helper functions in the unit tests build a canonical valid fixture and
mutate one field at a time, but always within the canonical shape. They
do not generate fixtures where the *relationship between two fields* is
broken. Mutation 1 in particular goes uncaught because there is no
fixture builder that lets a test construct "envelope-from-A,
record-claiming-B" — every fixture pulls both from the same issuer
parameter.

**The CRDT-state survivor (M4) is a different category — fixture decay.**
The test was constructed at a moment when a specific failure was
reproducible inside `bun test`. Whatever changed between then and now
— a dependency upgrade, a scheduling change in `@preact/signals`, an
internal Automerge timing tweak — broke the test's ability to fire,
without breaking the test itself. This is exactly the failure mode
described in the project's CLAUDE.md note: a green check that no longer
verifies the thing it claims to.

**Recommendations (for the user, not for Claude to act on now):**

1. **Add cross-field negative-construction tests** for revocation,
   signing envelopes, and any future authenticated-payload format.
   Pattern: build the envelope and payload from independently-supplied
   parameters, then assert that mismatched parameters are rejected.

2. **Add multi-target routing tests** to `message-router.test.ts`. At
   minimum: a `targets: [a, b]` route that asserts both ports received
   the message, and a `targets: [a, a]` route that asserts the
   duplicate behaviour is intentional (whichever way it goes).

3. **Audit "regression test against past bug" tests** for fidelity to
   their original failure. The crdt-state cycle test is the obvious
   one; there may be others. Where the original failure is
   timing-dependent, replace the high-level assertion with a lower-level
   invariant check that does not rely on the timing.

4. **Consider running this mutation suite on every PR.** Even five
   mutations per round, rotated across modules, would have caught two
   of these gaps the moment a test that should have covered them was
   merged but didn't.
