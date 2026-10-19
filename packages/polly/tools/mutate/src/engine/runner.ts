/**
 * Process execution: one `bun test` per mutant, a bounded pool, and a timeout
 * derived from each target's measured baseline.
 *
 * A fresh process per mutant is the floor Bun allows — `bun test` cannot be
 * re-entered in one process with a different module graph — but it costs tens
 * of milliseconds, and test selection keeps each run to the files that reach
 * the target.
 */
import { randomUUID } from "node:crypto";
import { existsSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { EngineRunner } from "./types.ts";

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
  /** Ask for Bun's junit report and return its XML (matrix mode). */
  junit?: boolean;
}

export interface BunTestOutcome {
  exitCode: number;
  timedOut: boolean;
  ms: number;
  stderrTail?: string;
  /** The junit XML; undefined when not asked for or not written (a crash). */
  junitXml?: string;
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

async function readJunit(path: string | undefined): Promise<string | undefined> {
  if (!path) return undefined;
  const file = Bun.file(path);
  if (!(await file.exists())) return undefined;
  const xml = await file.text();
  rmSync(path, { force: true });
  return xml;
}

/**
 * The argv for one test process. `bun-test` builds the `bun test` line;
 * `command` runs the configured argv whole and reaches every Bun process it
 * starts through BUN_OPTIONS, so `files`, `bail` and `junit` do not apply.
 */
function processArgv(
  runner: EngineRunner,
  run: BunTestRun,
  junitPath: string | undefined
): { argv: string[]; env: Record<string, string> } {
  if (runner.kind === "command") {
    const inherited = process.env["BUN_OPTIONS"];
    const preloads = run.preloads.map((p) => `--preload=${p}`).join(" ");
    return {
      argv: runner.argv,
      env: { ...run.env, BUN_OPTIONS: inherited ? `${inherited} ${preloads}` : preloads },
    };
  }
  return {
    argv: [
      "bun",
      "test",
      ...run.preloads.flatMap((p) => ["--preload", p]),
      ...(run.bail ? ["--bail"] : []),
      ...(junitPath ? ["--reporter=junit", `--reporter-outfile=${junitPath}`] : []),
      ...run.files,
    ],
    env: run.env ?? {},
  };
}

export async function runBunTest(
  run: BunTestRun,
  runner: EngineRunner = { kind: "bun-test" }
): Promise<BunTestOutcome> {
  const started = performance.now();
  const junitPath =
    run.junit && runner.kind === "bun-test"
      ? join(tmpdir(), `polly-mutate-junit-${randomUUID()}.xml`)
      : undefined;
  const { argv, env } = processArgv(runner, run, junitPath);
  // A command (`bun run bdd`) starts a process tree; its own group lets a
  // timeout kill the whole tree, not just the shell at the top.
  const group = runner.kind === "command";
  const proc = Bun.spawn(argv, {
    cwd: run.cwd,
    detached: group,
    env: cleanEnv(env),
    stdin: "ignore",
    stdout: "ignore",
    stderr: run.captureStderr ? "pipe" : "ignore",
  });
  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    if (group) process.kill(-proc.pid, 9);
    else proc.kill(9);
  }, run.timeoutMs);
  const stderrText =
    run.captureStderr && proc.stderr ? new Response(proc.stderr).text() : undefined;
  const exitCode = await proc.exited;
  clearTimeout(timer);
  const ms = performance.now() - started;
  const junitXml = await readJunit(junitPath);
  const outcome: BunTestOutcome = { exitCode, timedOut, ms, ...(junitXml ? { junitXml } : {}) };
  if (stderrText === undefined) return outcome;
  return { ...outcome, stderrTail: (await stderrText).slice(-2000) };
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
