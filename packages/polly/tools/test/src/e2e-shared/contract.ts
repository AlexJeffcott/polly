/**
 * The contract every tiered test case speaks.
 *
 * An e2e script is "tier-aware" when it exports an async `run(ctx)` that
 * returns a {@link TierResult} instead of signalling success through
 * `process.exitCode`. The engine prefers this export so it can collect a
 * structured result; scripts that do not export it still run (the engine
 * falls back to executing the file and reading its exit code), so the
 * migration is incremental and never breaks the suite.
 *
 * Standalone execution is preserved: a converted script keeps a
 * `if (import.meta.main) selfRun(run)` footer so `bun scripts/e2e-foo.ts`
 * behaves exactly as before.
 */

/** Logger handed to a case so its output can be captured/prefixed by the engine. */
export type TierLog = (message: string) => void;

/** Context passed to a case's `run()`. Kept small and forward-compatible. */
export interface TierContext {
  /** Emit a progress line. Defaults to `console.log` when run standalone. */
  log: TierLog;
  /** Extra environment the engine wants the case to honour (e.g. SIGNALING_URL). */
  env: Record<string, string | undefined>;
}

/** What a case reports back. `pass: false` with a `message` is a clean failure. */
export interface TierResult {
  pass: boolean;
  /** Human-readable failure reason; omitted on success. */
  message?: string;
  /** Optional structured detail surfaced in `--json` output. */
  detail?: Record<string, unknown>;
}

export type TierRun = (ctx: TierContext) => Promise<TierResult>;

/** Build a default context for standalone (`import.meta.main`) execution. */
export function standaloneContext(): TierContext {
  return {
    log: (message: string) => console.log(message),
    env: process.env,
  };
}

/**
 * Footer helper for converted scripts: runs the case standalone, prints a
 * PASS/FAIL line in the historical `[e2e] <capability>: PASS` format, and sets
 * the process exit code. Keeps the file runnable on its own.
 */
export async function selfRun(capability: string, run: TierRun): Promise<void> {
  const ctx = standaloneContext();
  try {
    const result = await run(ctx);
    if (result.pass) {
      ctx.log(`[e2e] ${capability}: PASS`);
    } else {
      ctx.log(`[e2e] ${capability}: FAIL — ${result.message ?? "no reason given"}`);
      process.exitCode = 1;
    }
  } catch (err) {
    ctx.log(`[e2e] ${capability}: FAIL — ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  }
}
