/**
 * Shared types for the Bun-native mutation engine (`polly mutate --engine bun`).
 *
 * Mutator names are Stryker's, on purpose: the report keeps the
 * mutation-testing-report-schema shape, so ingest/report/decisions and any
 * existing decisions.jsonl read the engine's output exactly as they read
 * Stryker's.
 */

export type MutatorName =
  | "ArithmeticOperator"
  | "ArrayDeclaration"
  | "BlockStatement"
  | "BooleanLiteral"
  | "ConditionalExpression"
  | "EqualityOperator"
  | "LogicalOperator"
  | "MethodExpression"
  | "OptionalChaining"
  | "StringLiteral"
  | "UnaryOperator"
  | "UpdateOperator";

/** One source edit: replace `[start, end)` of the target file's text with `replacement`. */
export interface Mutant {
  id: string;
  /** Absolute, symlink-resolved path of the mutated file. */
  file: string;
  mutatorName: MutatorName;
  start: number;
  end: number;
  replacement: string;
  /** 1-based, as mutation-testing-report-schema expects. */
  location: { start: Position; end: Position };
  /** Set when the mutant sits inside a polly verify primitive (polly#143). */
  ignoredReason?: string;
}

export interface Position {
  line: number;
  column: number;
}

export type MutantStatus =
  | "Killed"
  | "Survived"
  | "Timeout"
  | "NoCoverage"
  | "CompileError"
  | "RuntimeError"
  | "Ignored";

export interface MutantResult {
  mutant: Mutant;
  status: MutantStatus;
  statusReason?: string;
  durationMs?: number;
}

/** A target file, optionally narrowed to a line range (Stryker's `file.ts:10-20`). */
export interface MutateTarget {
  file: string;
  lines?: { from: number; to: number };
}

export interface EngineConfig {
  /** Directory `bun test` runs from; test globs and report paths are relative to it. */
  cwd: string;
  targets: MutateTarget[];
  /** Test-file globs (relative to cwd) the import graph starts from. */
  testInclude: string[];
  /**
   * The project's own test preloads (absolute), passed before the mutant
   * preload. Needed because a subset of test files can depend on a preload
   * the full suite happens to load some other way (polly's CSS-module shim).
   */
  testPreload: string[];
  concurrency: number;
  timeout: { factor: number; extraMs: number };
  /** Mark mutants inside requires/ensures/… as Ignored instead of running them. */
  ignoreVerifyCallsites: boolean;
  reportPath: string;
}

export interface TargetSummary {
  file: string;
  coveringTests: string[];
  baselineMs: number | null;
  results: MutantResult[];
}

export interface EngineResult {
  targets: TargetSummary[];
  wallMs: number;
  /**
   * Paths new to `git status` (relative to `root`), split by phase: written by
   * the unmutated baselines (the tests' own side effects) or by mutant runs
   * (a mutant redirected a write into the tree). Null outside a git worktree.
   * The report is written after the last snapshot, so it never appears here.
   */
  strayWrites: { root: string; baseline: string[]; mutants: string[] } | null;
}
