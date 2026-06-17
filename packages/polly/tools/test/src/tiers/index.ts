/**
 * Public surface of the tiered test engine.
 *
 * The engine is manifest-driven and reusable: feed it a {@link TierPlan} and it
 * runs the cases as isolated subprocesses with need-gating, parallelism, timing
 * and reporting. Polly's own dev suite (scripts/test) and the consumer-facing
 * `polly test` command are both front-ends over this.
 */

export { DEFAULT_JSON, parseTierArgs, type TierArgs } from "./args";
export { firstUnmetNeed, hasNeed } from "./detect";
export { discoverPlan } from "./discover";
export { runPlan } from "./engine";
export { orderCases } from "./order";
export { formatPlan, formatSummary, toJSON } from "./reporter";
export type {
  CaseExec,
  CaseOrder,
  CaseReport,
  CaseSpec,
  EngineOptions,
  Need,
  RunReport,
  Tier,
  TierPlan,
} from "./types";
