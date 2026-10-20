/**
 * Build the bun engine's config from the loaded mutation config
 * (`polly.mutate.ts`, or a Stryker JSON read through the migration mapping)
 * plus CLI flags.
 */
import { availableParallelism } from "node:os";
import { dirname, join, resolve } from "node:path";
import { Glob } from "bun";
import type { MutateArgs } from "./args.ts";
import type { MutateConfig } from "./config.ts";
import { MUTATION_CONFIG_FILE, type MutationConfig } from "./define.ts";
import type { CoverageMode, EngineConfig, EngineMode, MutateTarget } from "./engine/types.ts";

const RANGE = /^(.*?):(\d+)(?::\d+)?-(\d+)(?::\d+)?$/;

async function scanGlob(cwd: string, pattern: string): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Glob(pattern).scan({ cwd, absolute: true, onlyFiles: true })) {
    if (!f.includes("/node_modules/")) out.push(f);
  }
  return out;
}

function parseEntry(entry: string): { pattern: string; lines?: { from: number; to: number } } {
  const range = RANGE.exec(entry);
  if (!range?.[1]) return { pattern: entry };
  return { pattern: range[1], lines: { from: Number(range[2]), to: Number(range[3]) } };
}

/** Expand Stryker `mutate` entries: globs, `!` exclusions, and `file.ts:10-20` ranges. */
export async function expandMutateEntries(cwd: string, entries: string[]): Promise<MutateTarget[]> {
  const negated = entries.filter((x) => x.startsWith("!"));
  const excluded = new Set(
    (await Promise.all(negated.map((e) => scanGlob(cwd, e.slice(1))))).flat()
  );
  const targets = new Map<string, MutateTarget>();
  for (const entry of entries.filter((x) => !x.startsWith("!"))) {
    const { pattern, lines } = parseEntry(entry);
    const files = (await scanGlob(cwd, pattern)).filter((f) => !excluded.has(f));
    for (const f of files) targets.set(f, lines ? { file: f, lines } : { file: f });
  }
  return [...targets.values()].sort((a, b) => a.file.localeCompare(b.file));
}

async function changedSince(cwd: string, ref: string): Promise<Set<string>> {
  const proc = Bun.spawn(["git", "diff", "--name-only", "--relative", ref], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, code] = await Promise.all([new Response(proc.stdout).text(), proc.exited]);
  if (code !== 0)
    throw new Error(
      `git diff --name-only ${ref} failed: ${await new Response(proc.stderr).text()}`
    );
  return new Set(
    out
      .split("\n")
      .filter(Boolean)
      .map((p) => resolve(cwd, p))
  );
}

async function selectTargets(
  dir: string,
  config: MutationConfig,
  args: MutateArgs
): Promise<MutateTarget[]> {
  const entries = args.files
    ? args.files
        .split(",")
        .map((s) => s.trim())
        .filter(Boolean)
    : config.targets;
  const targets = await expandMutateEntries(dir, entries);
  if (!args.since) return targets;
  const changed = await changedSince(dir, args.since);
  return targets.filter((t) => changed.has(t.file));
}

function resolveConcurrency(flag: string | undefined, fromConfig: number | undefined): number {
  if (flag === undefined) return fromConfig ?? Math.max(1, availableParallelism() - 1);
  const n = Number(flag);
  if (!(Number.isInteger(n) && n > 0)) {
    throw new Error(`--concurrency must be a positive integer, got "${flag}"`);
  }
  return n;
}

function resolveMode(flag: string | undefined, config: MutationConfig): EngineMode {
  const mode = flag ?? config.mode ?? "fast";
  if (mode !== "fast" && mode !== "matrix") {
    throw new Error(`--mode ${mode}: expected fast or matrix`);
  }
  if (mode === "matrix" && config.runner?.kind === "command") {
    throw new Error("matrix mode needs per-test results; the command runner has none (use fast)");
  }
  return mode;
}

function resolveCoverage(flag: string | undefined, config: MutationConfig): CoverageMode {
  const coverage = flag ?? config.coverage ?? "dynamic";
  if (coverage !== "dynamic" && coverage !== "static") {
    throw new Error(`--coverage ${coverage}: expected dynamic or static`);
  }
  return coverage;
}

/** The engine's config from the loaded mutation config plus CLI flags (flags win). */
export async function engineConfigFor(cfg: MutateConfig, args: MutateArgs): Promise<EngineConfig> {
  if (!cfg.mutation) {
    throw new Error(
      cfg.mutationError ??
        `no ${MUTATION_CONFIG_FILE} found — run 'polly mutate init', or pass --config <path>`
    );
  }
  const { config, path } = cfg.mutation;
  const dir = dirname(path);
  const mode = resolveMode(args.mode, config);
  const command = config.runner?.kind === "command" ? config.runner : null;
  return {
    cwd: dir,
    targets: await selectTargets(dir, config, args),
    runner: command ?? { kind: "bun-test" },
    testInclude: config.tests?.include ?? [],
    testPreload: (config.tests?.preload ?? []).map((p) => resolve(dir, p)),
    mode,
    // The command runner reports no per-test results to attribute hits to.
    coverage: command ? "static" : resolveCoverage(args.coverage, config),
    concurrency: resolveConcurrency(args.concurrency, config.concurrency),
    timeout: config.timeout ?? { factor: 2, extraMs: 3000 },
    excludeMutators: config.mutators?.exclude ?? [],
    ignoreVerifyCallsites: config.ignoreVerifyCallsites ?? true,
    // A command runs where its package.json is; it gets no scratch cwd.
    scratchCwd: !(args.inTree || command),
    cacheDir: args.noCache ? null : join(dir, ".polly", "mutate", "cache"),
    reportPath: cfg.reportPath,
  };
}
