/**
 * Bounded-concurrency runner for a batch of independent subprocess steps.
 *
 * Each step is its own process, so a pool of N cuts a gate's wall-clock without
 * the steps interfering. The default captures each step's output and prints it
 * only if that step fails, so concurrent steps don't interleave into garbage;
 * `verbose` streams live instead, and the caller forces a pool of 1 so the
 * stream stays readable.
 *
 * `failFast` is *soft*: on the first failure the pool stops *claiming* new
 * steps, but the ≤ `concurrency - 1` already in flight run to completion — a
 * pool can't un-spawn them cleanly. With `failFast` off (the default, and the
 * right behaviour for a gate) every step runs and the full failure set is
 * reported.
 *
 * The scheduler takes an injectable {@link StepRunner} so it can be tested
 * deterministically: real millisecond subprocesses race the abort signal, so
 * soft-fail-fast skipping is only observable through a fake runner. Adapted
 * from lingua's devctl check-runner.
 */

/** One step in a batch: a named subprocess invocation. */
export interface BatchStep {
  /** Human-readable name shown in the progress line. */
  name: string;
  /** Argv to spawn. */
  cmd: string[];
  /** Working directory; defaults to the spawner's cwd. */
  cwd?: string;
}

export interface RunStepOptions {
  /** Stream output live instead of capturing it. Only valid serially. */
  verbose: boolean;
  /** Progress prefix, e.g. `[3/13] `. */
  prefix?: string;
  /**
   * Running under a pool: always capture (live streaming interleaves into
   * garbage when steps overlap) and suppress the in-place "running" line.
   */
  concurrent?: boolean;
}

export interface StepResult {
  ok: boolean;
  durationMs: number;
}

export interface BatchOptions {
  steps: BatchStep[];
  /** Stream each step's output live. Forces a serial pool. */
  verbose: boolean;
  /** Soft fail-fast: stop claiming new steps after the first failure. Default false. */
  failFast?: boolean;
  /** Max steps to run at once. Default 1 (serial). */
  concurrency?: number;
}

export interface BatchResult {
  ok: boolean;
  failed: string[];
  totalDurationMs: number;
}

const isTty = Boolean(process.stdout.isTTY);
const CHECK = "✅";
const CROSS = "❌";
const HOURGLASS = "⏳";
const ERASE_LINE = "\r[2K";

export function formatDuration(ms: number): string {
  return ms < 1_000 ? `${ms}ms` : `${(ms / 1_000).toFixed(1)}s`;
}

function flush(stream: WritableStreamLike, text: string): void {
  if (!text.trim()) return;
  stream.write(text.endsWith("\n") ? text : `${text}\n`);
}

interface WritableStreamLike {
  write(chunk: string): unknown;
}

/** Run one step, capturing or streaming its output per {@link RunStepOptions}. */
export async function runStep(step: BatchStep, options: RunStepOptions): Promise<StepResult> {
  const label = `${options.prefix ?? ""}${step.name}`;
  const start = Date.now();
  const concurrent = options.concurrent ?? false;

  // Live streaming only makes sense one step at a time; a pool always captures.
  if (options.verbose && !concurrent) {
    process.stdout.write(`\n── ${label} ──\n`);
    const proc = Bun.spawn(step.cmd, { cwd: step.cwd, stdout: "inherit", stderr: "inherit" });
    const exitCode = await proc.exited;
    const durationMs = Date.now() - start;
    process.stdout.write(
      `${exitCode === 0 ? CHECK : CROSS} ${label} (${formatDuration(durationMs)})\n`
    );
    return { ok: exitCode === 0, durationMs };
  }

  // The in-place "running" line clobbers siblings under a pool, so emit it only
  // when this step owns the line (serial mode).
  if (!concurrent) {
    process.stdout.write(isTty ? `${HOURGLASS} ${label}…` : `${HOURGLASS} ${label}…\n`);
  }

  const proc = Bun.spawn(step.cmd, { cwd: step.cwd, stdout: "pipe", stderr: "pipe" });
  const exitCode = await proc.exited;
  const durationMs = Date.now() - start;
  const stdoutText = await new Response(proc.stdout).text();
  const stderrText = await new Response(proc.stderr).text();

  if (!concurrent && isTty) process.stdout.write(ERASE_LINE);

  if (exitCode === 0) {
    process.stdout.write(`${CHECK} ${label} (${formatDuration(durationMs)})\n`);
    return { ok: true, durationMs };
  }

  process.stderr.write(`${CROSS} ${label} (${formatDuration(durationMs)})\n`);
  flush(process.stdout, stdoutText);
  flush(process.stderr, stderrText);
  return { ok: false, durationMs };
}

/**
 * Per-step executor used by the pool. Defaults to {@link runStep}; tests inject
 * a fake to drive the scheduler without spawning.
 */
export type StepRunner = (
  step: BatchStep,
  ctx: { verbose: boolean; prefix: string; concurrent: boolean }
) => Promise<StepResult>;

const defaultRunner: StepRunner = (step, ctx) => runStep(step, ctx);

/**
 * Drain `steps` through a bounded worker pool. Workers share a cursor, so at
 * most `concurrency` steps run at once; a pool of 1 is an ordinary serial loop.
 * Returns once every claimed step has settled.
 */
export async function runBatch(
  opts: BatchOptions,
  run: StepRunner = defaultRunner
): Promise<BatchResult> {
  const concurrency = Math.max(1, Math.floor(opts.concurrency ?? 1));
  const failFast = opts.failFast ?? false;
  const total = opts.steps.length;
  const workerCount = Math.min(concurrency, total);
  const failed: string[] = [];
  const start = Date.now();
  let next = 0;
  let aborted = false;

  const worker = async (): Promise<void> => {
    while (!aborted) {
      const i = next++;
      if (i >= total) return;
      const step = opts.steps[i];
      if (!step) continue;
      const prefix = `[${i + 1}/${total}] `;
      const result = await run(step, {
        verbose: opts.verbose,
        prefix,
        concurrent: concurrency > 1,
      });
      if (!result.ok) {
        failed.push(step.name);
        if (failFast) aborted = true;
      }
    }
  };

  await Promise.all(Array.from({ length: workerCount }, () => worker()));
  return { ok: failed.length === 0, failed, totalDurationMs: Date.now() - start };
}
