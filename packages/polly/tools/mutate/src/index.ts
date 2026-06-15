/**
 * @fairfox/polly/mutate — programmatic surface for mutation-testing analysis.
 *
 * The CLI (`polly mutate`) is the primary entry point; this barrel exposes the
 * reusable pieces for consumers who want to drive the analysis themselves:
 * ingest a mutation report into the kill matrix, derive the useless-test signals,
 * and assert the matrix contract.
 */

export { decide, type FileSignal, fileSignals, status } from "./decisions.ts";
export { buildDb, type MutationReport } from "./ingest.ts";
export { type InitResult, initConfig } from "./init.ts";
export { report } from "./report.ts";
export { isMatrixComplete, type MatrixCheck, verifyMatrix } from "./verify-matrix.ts";
