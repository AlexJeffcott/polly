/**
 * Process execution: one `bun test` per mutant, a bounded pool, and a timeout
 * derived from each target's measured baseline.
 *
 * A fresh process per mutant is the floor Bun allows — `bun test` cannot be
 * re-entered in one process with a different module graph — but it costs tens
 * of milliseconds, and test selection keeps each run to the files that reach
 * the target.
 */
import { existsSync } from "node:fs";

export interface BunTestRun {
  cwd: string;
  files: string[];
  /** Every `--preload`, in order; the mutant preload goes last. */
  preloads: string[];
  env?: Record<string, string>;
  bail: boolean;
  timeoutMs: number;
  /** Capture the tail of stderr (baselines only; mutant runs discard output). */
  captureStderr?: boolean;
}

export interface BunTestOutcome {
  exitCode: number;
  timedOut: boolean;
  ms: number;
  stderrTail?: string;
}

/** The preload as built (dist) or as source (monorepo / bun-run-from-source). */
export function preloadPath(): string {
  const candidates = [
    `${import.meta.dir}/preload.js`,
    `${import.meta.dir}/engine/preload.js`,
    `${import.meta.dir}/preload.ts`,
  ];
  const found = candidates.find((c) => existsSync(c));
  if (!found)
    throw new Error(`polly mutate: cannot find the engine preload (looked in ${import.meta.dir})`);
  return found;
}

function cleanEnv(extra: Record<string, string> | undefined): Record<string, string> {
  const env: Record<string, string> = {};
  for (const [k, v] of Object.entries(process.env)) {
    if (v !== undefined && !k.startsWith("POLLY_MUTATE_")) env[k] = v;
  }
  return { ...env, ...extra };
}

export async function runBunTest(run: BunTestRun): Promise<BunTestOutcome> {
  const started = performance.now();
  const argv = [
    "bun",
    "test",
    ...run.preloads.flatMap((p) => ["--preload", p]),
    ...(run.bail ? ["--bail"] : []),
    ...run.files,
  ];
  const proc = Bun.spawn(argv, {
    cwd: run.cwd,
    env: cleanEnv(run.env),
    stdin: "ignore",
    stdout: "ignore",
    stderr: run.captureStderr ? "pipe" : "ignore",
  });
  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    proc.kill(9);
  }, run.timeoutMs);
  const stderrText =
    run.captureStderr && proc.stderr ? new Response(proc.stderr).text() : undefined;
  const exitCode = await proc.exited;
  clearTimeout(timer);
  const ms = performance.now() - started;
  if (stderrText === undefined) return { exitCode, timedOut, ms };
  const text = await stderrText;
  return { exitCode, timedOut, ms, stderrTail: text.slice(-2000) };
}

/** Run `fn` over `items` with at most `concurrency` in flight; results keep input order. */
export async function pool<T, R>(
  items: readonly T[],
  concurrency: number,
  fn: (item: T, index: number) => Promise<R>
): Promise<R[]> {
  const results: R[] = new Array(items.length);
  let next = 0;
  const worker = async () => {
    while (next < items.length) {
      const i = next++;
      const item = items[i];
      if (item !== undefined) results[i] = await fn(item, i);
    }
  };
  await Promise.all(
    Array.from({ length: Math.max(1, Math.min(concurrency, items.length)) }, worker)
  );
  return results;
}
