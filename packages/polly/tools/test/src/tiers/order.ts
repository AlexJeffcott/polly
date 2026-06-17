/**
 * Within-tier case ordering.
 *
 * The engine drains a tier's cases through a bounded pool in array order, so
 * where a case sits decides when it launches. Reordering by a coarse cost hint
 * buys two different things depending on intent:
 *
 *   - "cost" (heaviest first): the long poles launch in the first `concurrency`
 *     slots and everything cheaper packs in behind them, so wall-clock collapses
 *     toward the single slowest case instead of the sum. Use for a full run.
 *   - "fast" (lightest first): cheap, high-signal cases run first, so under
 *     soft-fail-fast they trip the abort soonest — you can't un-spawn a 4-minute
 *     case, so you want it to *not* have started when a 2-second case fails.
 *   - "default": registry definition order, unchanged.
 *
 * Pure and dependency-free on purpose: this is the one piece of the engine that
 * is worth unit-testing in isolation, and keeping it out of engine.ts keeps the
 * subprocess-heavy engine off the unit-coverage table.
 */
import type { CaseOrder, CaseSpec } from "./types";

const COST_WEIGHT: Record<NonNullable<CaseSpec["cost"]>, number> = {
  light: 0,
  medium: 1,
  heavy: 2,
};

/** Weight of a case; unset cost is treated as "medium". */
function weightOf(spec: CaseSpec): number {
  return COST_WEIGHT[spec.cost ?? "medium"];
}

/**
 * Return a copy of `cases` reordered per `order`. Stable: cases of equal weight
 * keep their original relative order, and "default" returns the input as-is.
 */
export function orderCases(cases: CaseSpec[], order: CaseOrder): CaseSpec[] {
  if (order === "default") return cases;
  const direction = order === "cost" ? -1 : 1; // cost → heaviest first; fast → lightest first
  return cases
    .map((spec, index) => ({ spec, index }))
    .sort((a, b) => (weightOf(a.spec) - weightOf(b.spec)) * direction || a.index - b.index)
    .map((entry) => entry.spec);
}
