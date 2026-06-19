/**
 * @fairfox/polly/bdd — author executable Gherkin against polly's own model.
 *
 * The CLI (`polly bdd`) is the primary entry point; this barrel exposes the
 * pieces a consumer's step module needs (`defineStep`, `defineWorld`) plus the
 * programmatic surface for driving the runner and the verify cross-link.
 *
 * The binding declared by `defineStep` is dual-use — its `given`/`when`/`then`
 * drive the real factory bus, and its `message`/`stateExpr` are read statically
 * by the verify extractor. See tools/bdd/README.md.
 */

export { type DispatchBus, driveBus } from "./bus-driver.ts";
export { type CrossCheckResult, checkAgainstVerify } from "./check-verify.ts";
export { extractTraces } from "./extract.ts";
export { type ScenarioWitness, extractWitnesses } from "./witness.ts";
export { parseFeatureFile, parseFeatureText } from "./parse.ts";
export { type RunOptions, runFeatures } from "./run.ts";
export { defineStep, defineWorld, matchStep, registeredBindings } from "./steps.ts";
export type {
  BusLike,
  ParsedFeature,
  ParsedScenario,
  ParsedStep,
  RunResult,
  ScenarioResult,
  ScenarioTrace,
  SignalLike,
  StepBinding,
  StepFn,
  TraceStep,
  World,
  WorldDef,
} from "./types.ts";
