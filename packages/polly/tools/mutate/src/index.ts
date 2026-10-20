/**
 * @fairfox/polly/mutate — programmatic surface for mutation-testing analysis.
 *
 * The CLI (`polly mutate`) is the primary entry point; `defineMutation` types a
 * project's `polly.mutate.ts`. The rest is for consumers who want to drive the
 * engine or the analysis themselves:
 * ingest a mutation report into the kill matrix, derive the useless-test signals,
 * and assert the matrix contract.
 */

export { decide, type FileSignal, fileSignals, status } from "./decisions.ts";
export {
  type CommandRunner,
  defineMutation,
  loadMutationConfig,
  MUTATION_CONFIG_FILE,
  type MutationConfig,
  type MutationTests,
  parseMutationConfig,
} from "./define.ts";
export {
  applyMutant,
  buildImportGraph,
  type ContractSite,
  type ContractsMode,
  type ContractViolationRecord,
  coveringTests,
  type EngineConfig,
  type EngineHooks,
  type EngineResult,
  findTestFiles,
  generateMutants,
  type Mutant,
  type MutantResult,
  type MutantStatus,
  type MutateTarget,
  type MutatorName,
  mutationScore,
  runEngine,
  VERIFY_PRIMITIVES,
} from "./engine/index.ts";
export { buildDb, type MutationReport, type ReportContracts } from "./ingest.ts";
export { type InitResult, initConfig } from "./init.ts";
export { type Migration, migrateConfig, strykerToMutation } from "./migrate.ts";
export { report } from "./report.ts";
export { isMatrixComplete, type MatrixCheck, verifyMatrix } from "./verify-matrix.ts";
