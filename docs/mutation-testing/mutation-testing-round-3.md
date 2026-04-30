# Mutation Testing — Round 3

Targets: primitive-registry, schema-version, mesh-network-adapter,
pairing, keyring-storage. The hypothesis going in was that this set
would be the strongest covered — every module has a dedicated test
file and obvious specification — and we'd see a high catch rate.

| #  | File                       | Category                       | Result    |
|----|----------------------------|--------------------------------|-----------|
| 11 | primitive-registry.ts      | Disabled invariant throw       | caught    |
| 12 | schema-version.ts          | Off-by-one in boundary check   | caught    |
| 13 | mesh-network-adapter.ts    | Removed security drop          | caught    |
| 14 | pairing.ts                 | Off-by-one in expiry           | SURVIVED  |
| 15 | keyring-storage.ts         | Field-swap on deserialise      | caught    |

1 survivor, 4 caught. The single survivor was the smallest
mutation in the round (one operator).

---

## Mutation 11 — primitive-registry.ts: disable collision throw

**Location:** `src/shared/lib/primitive-registry.ts:103`

**Change:** removed the `PrimitiveCollisionError` throw branch from
`register`. Two primitives can now claim the same key with no error.

**Result:** caught. 11 failures across the dedicated registry tests
and the consumer tests in peer-state and mesh-state that share the
process-wide singleton.

**Test quality:** the registry's own suite has both halves of the
contract — same-primitive re-registration is a no-op, different-primitive
re-registration throws — and the consumers re-assert at their layer.
This is the multi-layer test pattern that makes the bug expensive to
sneak past.

---

## Mutation 12 — schema-version.ts: `>` → `>=`

**Location:** `src/shared/lib/schema-version.ts:141`

**Change:** flipped the doc-version comparator so a document at the
target version is now classified as ahead of the application. The
"already at target, no migration needed" path now throws.

**Result:** caught. 3 failures in `runMigrations` boundary tests. One
of them — "stamps the target version even when no migrations run" —
is the canonical "doc at exactly the target" assertion.

**Test quality:** `crdt-state.test.ts:212` has the boundary-equal test
that the change to `>=` breaks immediately. Boundary equality is the
class of bug an off-by-one mutation produces, and the test asserts
exactly that case.

---

## Mutation 13 — mesh-network-adapter.ts: drop revoked-peer drop

**Location:** `src/shared/lib/mesh-network-adapter.ts:237`

**Change:** removed the `if (this.keyring.revokedPeers.has(...)) return
undefined` short-circuit. Messages from revoked peers are now still
verified and forwarded as long as the public key is in `knownPeers`.

**Result:** caught. 2 failures in `MeshNetworkAdapter — revocation
enforcement`:

- `a document written by a revoked peer never reaches the other side`
- `applying a revocation at runtime stops further messages from the target`

**Test quality:** end-to-end through-the-adapter integration tests
that exercise the actual code path being relied on for security.
Notable contrast with Round 1 M1 (revocation issuer/sender check):
that mutation lived one layer deeper in the same subsystem and went
undetected, while this one — which lives in the network-adapter
choke point — is well-covered. The coverage is real but uneven
inside one feature.

---

## Mutation 14 — pairing.ts: `>=` → `>` in `isPairingTokenExpired`

**Location:** `src/shared/lib/pairing.ts:176`

**Change:** flipped the boundary so a token at exactly its `expiresAt`
millisecond is considered valid rather than expired.

**Result:** **SURVIVED.** 661 / 661 pass.

**Why it survived:** none of the `pairing.test.ts` tests construct a
token whose `expiresAt` is exactly the current `now()`. Every existing
test uses `now()` either well before `expiresAt` (token valid) or
well after (token expired). The boundary case — `now() === expiresAt`
— is the case the mutation broke, and there is no assertion against
that specific equality.

**Severity:** low in practical terms (a single millisecond window),
but the same class of mutation (flipped boundary inclusion) on a TTL
or auth-window field is exactly the kind of bug that ships and then
shows up as flaky tests in production. The principle matters more
than this instance.

**Test gap:** missing boundary-equal assertion. Same category as
Round 1 M3 (no `targets.length > 1` test) and Round 2 M9 (no return
value assertion) — every one of these survivors is the test missing
a test case that exactly straddles the line the production code is
meant to draw.

---

## Mutation 15 — keyring-storage.ts: swap publicKey/secretKey

**Location:** `src/shared/lib/keyring-storage.ts:115`

**Change:** in `deserialiseKeyring`, fed the encoded secretKey into
`identity.publicKey` and vice versa. The keyring round-trips bytes
but the `identity` is now nonsense — signing produces invalid
signatures because `secretKey` is actually a 32-byte public key and
the function will throw a `SigningError("invalid-secret-key")` since
public keys are 32 bytes, not 64.

**Result:** caught. 4 failures across `keyring-storage.test.ts`
(round-trip), `fileKeyringStorage` (file write), and the CLI bootstrap
flow.

**Test quality:** good — the round-trip test hashes-and-verifies via
the actual signing path, so swapped keys break verification, not just
"the bytes are different." The fact that the bootstrap flow tests
also broke shows that the unit assertion is not the only line of
defence.

---

## Round-3 Findings

**The single survivor (M14) follows the exact pattern of every
Round-1 and Round-2 survivor:** the production code draws a line
("expired iff t ≥ expiry"), the existing tests assert behaviour on
both sides of the line ("now < expiry" passes; "now > expiry+1"
fails), but no test asserts the exact-on-the-line case. Off-by-one
mutations that move the inclusivity slip through every time.

**The four caught mutations all had a test whose name was the
specification.** Same observation as Round 2: when a behaviour has a
single-sentence contract, a test titled with that contract that
asserts the behaviour itself (not a side-effect) is what catches
the bug.

**Cumulative pattern across rounds 1-3:** every survivor so far is
either
- a missing boundary-equal case (R1-M3, R3-M14),
- a return-value not asserted (R2-M9),
- a cross-field invariant not constructed (R1-M1),
- a side-effect-not-value assertion (R3-M14 again on `>=`),
- or a regression test that has decoupled from its original failure
  (R1-M4),
- or a property that only matters across subsystems and is therefore
  invisible to a per-module test (R2-M7).
