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
  | "ArrowFunction"
  | "AssignmentOperator"
  | "BlockStatement"
  | "BooleanLiteral"
  | "ConditionalExpression"
  | "EqualityOperator"
  | "LogicalOperator"
  | "MethodExpression"
  | "ObjectLiteral"
  | "OptionalChaining"
  | "Regex"
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
  /** Matrix mode: ids (see junit.ts `testId`) of every test that failed under the mutant. */
  killedBy?: string[];
}

/** One test the baseline ran (matrix mode). */
export interface TestRef {
  id: string;
  /** Absolute path of the test file. */
  file: string;
  name: string;
  line: number;
}

/**
 * fast    `--bail`: stop at the first failing test; status only.
 * matrix  no bail, junit per run: every killing test, for the redundancy analysis.
 */
export type EngineMode = "fast" | "matrix";

/** A target file, optionally narrowed to a line range (Stryker's `file.ts:10-20`). */
export interface MutateTarget {
  file: string;
  lines?: { from: number; to: number };
}

export type EngineRunner = { kind: "bun-test" } | { kind: "command"; argv: string[] };

export interface EngineConfig {
  /** Directory `bun test` runs from; test globs and report paths are relative to it. */
  cwd: string;
  targets: MutateTarget[];
  /**
   * bun-test  `bun test` on the test files that reach each target.
   * command   the argv, whole, for every mutant (polly.mutate.ts `runner`).
   */
  runner: EngineRunner;
  /** Test-file globs (relative to cwd) the import graph starts from. */
  testInclude: string[];
  /**
   * The project's own test preloads (absolute), passed before the mutant
   * preload. Needed because a subset of test files can depend on a preload
   * the full suite happens to load some other way (polly's CSS-module shim).
   */
  testPreload: string[];
  mode: EngineMode;
  concurrency: number;
  timeout: { factor: number; extraMs: number };
  /** Mutators that generate nothing. */
  excludeMutators: MutatorName[];
  /** Mark mutants inside requires/ensures/… as Ignored instead of running them. */
  ignoreVerifyCallsites: boolean;
  /**
   * Run each test process in a fresh scratch cwd (workdir.ts), so a mutant's
   * relative writes miss the repo. False runs everything in `cwd`.
   */
  scratchCwd: boolean;
  /** Result cache directory (cache.ts); null runs everything. */
  cacheDir: string | null;
  reportPath: string;
}

export interface TargetSummary {
  file: string;
  coveringTests: string[];
  baselineMs: number | null;
  /** Its mutants ran in the project cwd (scratch off, or its tests need the cwd). */
  inTree: boolean;
  /** Results came from the cache; nothing ran. */
  cached: boolean;
  /** Matrix mode: every test the baseline ran, plus any load-failure stand-in a mutant named. */
  tests: TestRef[];
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
