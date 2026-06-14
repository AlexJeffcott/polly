/**
 * @fairfox/polly/test/coverage — programmatic API behind `polly coverage`.
 *
 * Use the CLI (`polly coverage`) for the common case; import these to script
 * the policy yourself or to add a coverage tier to a custom runner.
 */

export { type LoadedConfig, loadCoverageConfig } from "./discover";
export {
  type CoverageFindings,
  type CoverageRow,
  enforceCoverage,
  evaluateCoverage,
  hasFailure,
  parseCoverageTable,
  runCoverage,
  type Violation,
} from "./enforce";
export {
  findStrykerConfigs,
  type MutateTargetIssue,
  type MutateTargetReport,
  validateMutateTargets,
} from "./mutate-targets";
export type { CoverageConfig, ExemptEntry, FileThreshold } from "./types";
