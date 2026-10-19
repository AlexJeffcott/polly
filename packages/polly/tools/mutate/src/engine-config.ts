/**
 * Build the bun engine's config from what `polly mutate` already knows: the
 * Stryker config (`mutate`, `bun.testFiles`, `concurrency`) plus CLI flags.
 *
 * Interim: a typed `polly.mutate.ts` replaces the Stryker config as the source
 * in a later step. Until then the bun engine reads the same file Stryker does,
 * so both engines mutate the same targets.
 */
import { availableParallelism } from "node:os";
import { dirname, resolve } from "node:path";
import { Glob } from "bun";
import { isRecord } from "../../../src/shared/lib/guards";
import type { MutateArgs } from "./args.ts";
import type { MutateConfig } from "./config.ts";
import type { EngineConfig, MutateTarget } from "./engine/types.ts";

const RANGE = /^(.*?):(\d+)(?::\d+)?-(\d+)(?::\d+)?$/;

function stringArray(value: unknown): string[] {
  return Array.isArray(value) ? value.filter((v): v is string => typeof v === "string") : [];
}

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

interface StrykerShape {
  cwd: string;
  testInclude: string[];
  testPreload: string[];
  mutate: string[];
  concurrency: number | undefined;
}

/**
 * `--preload <p>` / `--preload=<p>` pairs from the bun runner's `nodeArgs`,
 * which it passes to `bun test` — so one config entry serves both engines.
 */
export function preloadsFromNodeArgs(cwd: string, nodeArgs: string[]): string[] {
  const out: string[] = [];
  nodeArgs.forEach((arg, i) => {
    const value =
      arg === "--preload"
        ? nodeArgs[i + 1]
        : arg.startsWith("--preload=")
          ? arg.slice(10)
          : undefined;
    if (value) out.push(resolve(cwd, value));
  });
  return out;
}

async function readStrykerShape(path: string): Promise<StrykerShape> {
  const raw: unknown = await Bun.file(path).json();
  if (!isRecord(raw)) throw new Error(`${path} is not a JSON object`);
  const runner = raw["testRunner"];
  if (runner !== undefined && runner !== "bun") {
    throw new Error(
      `testRunner "${String(runner)}": the bun engine drives \`bun test\` only for now`
    );
  }
  const bun = isRecord(raw["bun"]) ? raw["bun"] : {};
  const testInclude = stringArray(bun["testFiles"]);
  if (testInclude.length === 0) throw new Error(`${path} has no bun.testFiles`);
  return {
    cwd: dirname(path),
    testInclude,
    testPreload: preloadsFromNodeArgs(dirname(path), stringArray(bun["nodeArgs"])),
    mutate: stringArray(raw["mutate"]),
    concurrency: typeof raw["concurrency"] === "number" ? raw["concurrency"] : undefined,
  };
}

async function selectTargets(shape: StrykerShape, args: MutateArgs): Promise<MutateTarget[]> {
  const entries = args.files
    ? args.files
        .split(",")
        .map((s) => s.trim())
        .filter(Boolean)
    : shape.mutate;
  const targets = await expandMutateEntries(shape.cwd, entries);
  if (!args.since) return targets;
  const changed = await changedSince(shape.cwd, args.since);
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

export async function engineConfigFromStryker(
  cfg: MutateConfig,
  args: MutateArgs
): Promise<EngineConfig> {
  if (args.mode && args.mode !== "fast") {
    throw new Error(
      `--mode ${args.mode}: the bun engine runs in fast mode only for now; use --engine stryker for a kill matrix`
    );
  }
  if (!cfg.strykerConfigPath) {
    throw new Error(
      "no stryker.conf.json found — run 'polly mutate init', or pass --config <path>"
    );
  }
  const shape = await readStrykerShape(cfg.strykerConfigPath);
  return {
    cwd: shape.cwd,
    targets: await selectTargets(shape, args),
    testInclude: shape.testInclude,
    testPreload: shape.testPreload,
    concurrency: resolveConcurrency(args.concurrency, shape.concurrency),
    timeout: { factor: 2, extraMs: 3000 },
    ignoreVerifyCallsites: true,
    reportPath: cfg.reportPath,
  };
}
