/**
 * `polly.mutate.ts` — the typed config for `polly mutate`:
 *
 *   import { defineMutation } from "@fairfox/polly/mutate";
 *   export default defineMutation({
 *     targets: ["src/**\/*.ts", "!src/**\/*.test.ts"],
 *     tests: { include: ["tests/**\/*.test.ts"] },
 *   });
 *
 * Paths are relative to the config file's directory, which is also where the
 * tests run. `defineMutation` only checks the shape at the type level; the
 * CLI loads the file with a plain dynamic import and validates the default
 * export with `parseMutationConfig`, so a hand-written `.js` config with a
 * typo fails with a message, not a crash deep in the engine.
 */
import { isRecord } from "../../../src/shared/lib/guards";
import type { ContractsMode, CoverageMode, EngineMode, MutatorName } from "./engine/types.ts";

export const MUTATION_CONFIG_FILE = "polly.mutate.ts";

export interface MutationTests {
  /** Test-file globs. The engine runs only the files whose imports reach a target. */
  include: string[];
  /** Project preloads, passed to `bun test` before the injection preload. */
  preload?: string[];
}

export interface CommandRunner {
  kind: "command";
  /**
   * The command, run once per mutant in the config dir; non-zero exit kills
   * the mutant. Every Bun process it starts gets the injection preload via
   * BUN_OPTIONS. No test selection, fast mode only.
   */
  argv: string[];
}

interface MutationCommon {
  /** Files to mutate: globs, `!` exclusions, and `file.ts:10-20` line ranges. */
  targets: string[];
  /** fast stops at the first failing test; matrix records every killer. Default fast. */
  mode?: EngineMode;
  /**
   * dynamic: one probed pass over every test file finds the tests that run
   * each mutant; a mutant no test runs is NoCoverage. static: the test files
   * that import the target. Default dynamic; the command runner is always static.
   */
  coverage?: CoverageMode;
  /** Parallel test processes. Default: cores − 1. */
  concurrency?: number;
  /** Per-mutant timeout = baseline × factor + extraMs. Default 2 / 3000. */
  timeout?: { factor: number; extraMs: number };
  mutators?: { exclude?: MutatorName[] };
  /**
   * Report mutants the project's TypeScript config rejects as CompileError,
   * never run (TypeScript 7 through the `typescript-7` dependency). Default true.
   */
  typecheck?: boolean;
  /** Report mutants inside requires/ensures/… as Ignored (polly#143). Default true. */
  ignoreVerifyCallsites?: boolean;
  /**
   * POLLY_CONTRACTS for every test process: a false requires/ensures throws,
   * so each contract kills the mutants that falsify it. off keeps them
   * no-ops; ensures enforces postconditions only. Default all.
   */
  contracts?: ContractsMode;
  /** `polly mutate run` exits 1 when the score is below `break`. */
  thresholds?: { break?: number };
  /** Report path. Default reports/mutation/mutation.json. */
  report?: string;
  /** Verdict log. Default .polly/test-debt/decisions.jsonl. */
  decisions?: string;
}

export type MutationConfig = MutationCommon &
  (
    | { runner?: { kind: "bun-test" }; tests: MutationTests }
    | { runner: CommandRunner; tests?: undefined }
  );

export function defineMutation(config: MutationConfig): MutationConfig {
  return config;
}

const MUTATOR_NAMES: ReadonlySet<string> = new Set<MutatorName>([
  "ArithmeticOperator",
  "ArrayDeclaration",
  "ArrowFunction",
  "AssignmentOperator",
  "BlockStatement",
  "BooleanLiteral",
  "ConditionalExpression",
  "EqualityOperator",
  "LogicalOperator",
  "MethodExpression",
  "ObjectLiteral",
  "OptionalChaining",
  "Regex",
  "StringLiteral",
  "UnaryOperator",
  "UpdateOperator",
]);

function isMutatorName(value: unknown): value is MutatorName {
  return typeof value === "string" && MUTATOR_NAMES.has(value);
}

function strings(value: unknown, where: string): string[] {
  if (!Array.isArray(value) || !value.every((v) => typeof v === "string")) {
    throw new Error(`${where} must be an array of strings`);
  }
  return value;
}

function optionalNumber(value: unknown, where: string): number | undefined {
  if (value === undefined) return undefined;
  if (typeof value !== "number" || !Number.isFinite(value))
    throw new Error(`${where} must be a number`);
  return value;
}

function optionalString(value: unknown, where: string): string | undefined {
  if (value === undefined) return undefined;
  if (typeof value !== "string") throw new Error(`${where} must be a string`);
  return value;
}

function isEngineMode(v: unknown): v is EngineMode {
  return v === "fast" || v === "matrix";
}

function isCoverageMode(v: unknown): v is CoverageMode {
  return v === "dynamic" || v === "static";
}

function parseRun(raw: Record<string, unknown>, where: string): MutationCommon {
  const mode = raw["mode"];
  if (mode !== undefined && !isEngineMode(mode)) {
    throw new Error(`${where}: mode must be "fast" or "matrix"`);
  }
  const concurrency = optionalNumber(raw["concurrency"], `${where}: concurrency`);
  if (concurrency !== undefined && !(Number.isInteger(concurrency) && concurrency > 0)) {
    throw new Error(`${where}: concurrency must be a positive integer`);
  }
  const coverage = raw["coverage"];
  if (coverage !== undefined && !isCoverageMode(coverage)) {
    throw new Error(`${where}: coverage must be "dynamic" or "static"`);
  }
  const common: MutationCommon = { targets: strings(raw["targets"], `${where}: targets`) };
  if (isEngineMode(mode)) common.mode = mode;
  if (isCoverageMode(coverage)) common.coverage = coverage;
  if (concurrency !== undefined) common.concurrency = concurrency;
  const timeout = raw["timeout"];
  if (timeout !== undefined) {
    if (!isRecord(timeout)) throw new Error(`${where}: timeout must be { factor, extraMs }`);
    const factor = optionalNumber(timeout["factor"], `${where}: timeout.factor`) ?? 2;
    const extraMs = optionalNumber(timeout["extraMs"], `${where}: timeout.extraMs`) ?? 3000;
    common.timeout = { factor, extraMs };
  }
  return common;
}

function parseMutants(raw: Record<string, unknown>, where: string): Partial<MutationCommon> {
  const out: Partial<MutationCommon> = {};
  const mutators = raw["mutators"];
  if (mutators !== undefined) {
    if (!isRecord(mutators)) throw new Error(`${where}: mutators must be { exclude }`);
    const exclude = mutators["exclude"] === undefined ? [] : mutators["exclude"];
    if (!Array.isArray(exclude) || !exclude.every(isMutatorName)) {
      throw new Error(`${where}: mutators.exclude holds an unknown mutator name`);
    }
    out.mutators = { exclude };
  }
  const ignore = raw["ignoreVerifyCallsites"];
  if (ignore !== undefined) {
    if (typeof ignore !== "boolean")
      throw new Error(`${where}: ignoreVerifyCallsites must be boolean`);
    out.ignoreVerifyCallsites = ignore;
  }
  const typecheck = raw["typecheck"];
  if (typecheck !== undefined) {
    if (typeof typecheck !== "boolean") throw new Error(`${where}: typecheck must be boolean`);
    out.typecheck = typecheck;
  }
  return { ...out, ...parseContracts(raw, where) };
}

export function isContractsMode(v: unknown): v is ContractsMode {
  return v === "off" || v === "ensures" || v === "all";
}

function parseContracts(raw: Record<string, unknown>, where: string): Partial<MutationCommon> {
  const contracts = raw["contracts"];
  if (contracts === undefined) return {};
  if (!isContractsMode(contracts)) {
    throw new Error(`${where}: contracts must be "off", "ensures" or "all"`);
  }
  return { contracts };
}

function parseOutputs(raw: Record<string, unknown>, where: string): Partial<MutationCommon> {
  const out: Partial<MutationCommon> = {};
  const thresholds = raw["thresholds"];
  if (thresholds !== undefined) {
    if (!isRecord(thresholds)) throw new Error(`${where}: thresholds must be { break }`);
    const brk = optionalNumber(thresholds["break"], `${where}: thresholds.break`);
    out.thresholds = brk === undefined ? {} : { break: brk };
  }
  const report = optionalString(raw["report"], `${where}: report`);
  if (report !== undefined) out.report = report;
  const decisions = optionalString(raw["decisions"], `${where}: decisions`);
  if (decisions !== undefined) out.decisions = decisions;
  return out;
}

function parseCommon(raw: Record<string, unknown>, where: string): MutationCommon {
  return { ...parseRun(raw, where), ...parseMutants(raw, where), ...parseOutputs(raw, where) };
}

/** Validate a loaded config's default export. `where` names the file in errors. */
export function parseMutationConfig(raw: unknown, where: string): MutationConfig {
  if (!isRecord(raw)) throw new Error(`${where}: the default export must be a config object`);
  // targets, then runner/tests, then the rest: the order a rendered config reads in.
  const { targets, ...common } = parseCommon(raw, where);
  const runner = raw["runner"];
  if (isRecord(runner) && runner["kind"] === "command") {
    const argv = strings(runner["argv"], `${where}: runner.argv`);
    if (argv.length === 0) throw new Error(`${where}: runner.argv is empty`);
    return { targets, runner: { kind: "command", argv }, ...common };
  }
  if (runner !== undefined && !(isRecord(runner) && runner["kind"] === "bun-test")) {
    throw new Error(`${where}: runner.kind must be "bun-test" or "command"`);
  }
  const tests = raw["tests"];
  if (!isRecord(tests)) throw new Error(`${where}: tests.include is required`);
  const include = strings(tests["include"], `${where}: tests.include`);
  if (include.length === 0) throw new Error(`${where}: tests.include is empty`);
  const preload =
    tests["preload"] === undefined
      ? undefined
      : strings(tests["preload"], `${where}: tests.preload`);
  return { targets, tests: preload ? { include, preload } : { include }, ...common };
}

/** Import a `polly.mutate.ts` (or `.js`) and validate its default export. */
export async function loadMutationConfig(path: string): Promise<MutationConfig> {
  const mod: unknown = await import(path);
  const raw = isRecord(mod) ? mod["default"] : undefined;
  return parseMutationConfig(raw, path);
}
