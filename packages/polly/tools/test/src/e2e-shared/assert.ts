/**
 * One assertion primitive for every e2e script.
 *
 * Six scripts each declared their own `class AssertionError extends Error {}`
 * plus an `assert()` function. This is the single shared copy. A thrown
 * {@link Failure} is the canonical "clean test failure" signal: the `selfRun`
 * footer and the tier engine both treat it as `pass: false` rather than a
 * crash, so the distinction between "the assertion didn't hold" and "the
 * harness threw" stays visible.
 */

/** Thrown when an assertion does not hold. Distinct type so callers can catch it. */
export class Failure extends Error {
  override name = "Failure";
}

/** Assert `condition`, throwing {@link Failure} with `message` when it is false. */
export function assert(condition: unknown, message: string): asserts condition {
  if (!condition) throw new Failure(message);
}

/** Fail unconditionally. `never` return lets it stand in for exhaustiveness. */
export function fail(message: string): never {
  throw new Failure(message);
}
