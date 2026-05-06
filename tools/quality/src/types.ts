/**
 * Plugin-host contract for `@fairfox/polly/quality`.
 *
 * A `QualityPlugin` bundles a set of `Check`s under a namespace. The host
 * loads one or more plugins from `polly.config.ts`, validates that each
 * check's id is unique, and runs the requested set in parallel. A check
 * declares the inputs it reads so the cache layer (see `cache.ts`) can
 * compute a content-hash and skip re-execution when nothing has changed.
 *
 * Plugin and check ids are namespaced as `<plugin>:<name>`. Polly's own
 * plugin uses the `polly` prefix; polly-ui will use `polly-ui`; consumer
 * plugins use whatever prefix matches their package name.
 */

/**
 * Outcome of running a single check. The host aggregates these into a
 * `RunReport` for the CLI. `cached` is true when the result came back from
 * the on-disk cache without re-running the check body.
 */
export type CheckRunResult = {
  id: string;
  ok: boolean;
  durationMs: number;
  cached: boolean;
  /** Human-readable summary line (one violation per element, or status). */
  messages: string[];
  /** Raw error if the check threw; surfaces in CLI output. */
  error?: string;
};

/**
 * Context passed to a check at run time. The host fills in `rootDir`
 * and `signal` (for cancellation) before invoking `run`.
 */
export type CheckContext<TConfig = unknown> = {
  /** Repository root the consumer is checking. */
  rootDir: string;
  /** Resolved configuration for this check (already validated). */
  config: TConfig;
  /** Aborted when the run is cancelled (CLI Ctrl-C, watch reload, etc.). */
  signal?: AbortSignal;
};

/**
 * A single check. The host calls `validate(config)` once at load time
 * and `run(ctx)` once per execution. `filesRead(config)` is consulted by
 * the cache before `run` — return the absolute paths whose content must
 * invalidate a cached result.
 */
export type Check<TConfig = unknown> = {
  /** Namespaced id, e.g. `polly:no-as-casting`. */
  id: string;
  /** One-line description for `polly quality list`. */
  description: string;
  /**
   * Validate user-supplied config. Return `null` for valid input or a
   * non-empty array of error messages for invalid input. Errors are
   * surfaced at load time, not at run time.
   */
  validate?: (config: unknown) => string[] | null;
  /**
   * Files whose content affects the result of this check. Returned as
   * absolute paths (or paths relative to `rootDir`; the cache normalises).
   * The host hashes these and skips `run` on cache hit.
   */
  filesRead?: (config: TConfig, rootDir: string) => Promise<string[]> | string[];
  /**
   * Environment variables and tool versions that contribute to the
   * cache key alongside file content. Use this when the check's behaviour
   * depends on something not captured by `filesRead` (e.g. a binary's
   * version, an env var that flips a code path).
   */
  cacheKeyExtras?: (config: TConfig) => Record<string, string>;
  /** Run the check. Throws are caught by the host and reported as failures. */
  run: (ctx: CheckContext<TConfig>) => Promise<CheckOutcome>;
};

/**
 * The body of a check returns either pass or fail with messages. The host
 * adds id, duration, and cache status to produce a `CheckRunResult`.
 */
export type CheckOutcome = {
  ok: boolean;
  messages: string[];
};

/**
 * A plugin contributes a namespaced bundle of checks.
 */
export type QualityPlugin = {
  /** Namespace used as the prefix on every check id. */
  name: string;
  version: string;
  checks: Check<unknown>[];
};

/**
 * Per-check configuration map keyed by check id. The host pulls the
 * matching entry out of `qualityConfig` and passes it as `ctx.config`.
 */
export type QualityRunConfig = {
  plugins: QualityPlugin[];
  /** Per-check config keyed by check id (e.g. `"polly:no-as-casting"`). */
  checks?: Record<string, unknown>;
};

export type RunReport = {
  ok: boolean;
  results: CheckRunResult[];
  totalDurationMs: number;
};
