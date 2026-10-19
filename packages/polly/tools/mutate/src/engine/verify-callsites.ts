/**
 * The polly verify primitives whose argument expressions are runtime no-ops.
 * A mutation anywhere inside a call to one of these cannot be killed by a test,
 * so its mutants are excluded from scoring (polly#143).
 *
 * The single source for both engines: the Stryker ignorer in
 * tools/verify/src/stryker re-exports this set.
 */
export const VERIFY_PRIMITIVES: ReadonlySet<string> = new Set([
  "requires",
  "ensures",
  "invariant",
  "stateConstraint",
  "forAllPeers",
  "somePeer",
]);

export function verifyCallsiteReason(name: string): string {
  return (
    `Inside polly's ${name}(...) — a runtime no-op (compiled away in production, ` +
    `translated to a TLA+ assertion in verification). No test can observe or kill ` +
    `mutations here, so they are excluded from the score (polly#143).`
  );
}
