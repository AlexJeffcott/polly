/**
 * Timeout budgets and the margin left against them.
 *
 * A fixed per-case timeout silently tightens every time the work it wraps
 * grows. `coverage.enforce` re-runs the whole unit suite under `--coverage`,
 * so its cost tracks that suite's size: it drifted to 83–86% of a 180s cap,
 * then crossed the line under load and failed an `--all` run that had no
 * coverage regression in it (polly#175).
 *
 * A duration is only legible next to its budget. The engine records
 * `timeoutMs` on every case report, and reports the ratio out loud once a
 * case passes {@link BUDGET_WARN_FRACTION} of it — so the margin erodes
 * visibly, one run at a time, instead of arriving as a red run.
 */

/** Report the margin once a case has consumed this much of its budget. */
export const BUDGET_WARN_FRACTION = 0.7;

/**
 * Fraction of its timeout a case consumed, or `undefined` when there is no
 * budget to measure against.
 */
export function budgetUse(durationMs: number, timeoutMs: number | undefined): number | undefined {
  if (typeof timeoutMs !== "number" || timeoutMs <= 0) return undefined;
  return durationMs / timeoutMs;
}

/**
 * A short "how close was that" note, or `undefined` when the case sat below
 * {@link BUDGET_WARN_FRACTION} and the margin needs no comment.
 *
 * @example
 * ```typescript
 * formatBudgetUse(154_235, 180_000); // "86% of its 180000ms timeout budget"
 * formatBudgetUse(4_633, 180_000); // undefined
 * ```
 */
export function formatBudgetUse(
  durationMs: number,
  timeoutMs: number | undefined
): string | undefined {
  const used = budgetUse(durationMs, timeoutMs);
  if (used === undefined || used < BUDGET_WARN_FRACTION) return undefined;
  return `${Math.round(used * 100)}% of its ${timeoutMs}ms timeout budget`;
}
