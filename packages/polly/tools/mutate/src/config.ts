/**
 * Resolve the config and paths `polly mutate` works with.
 *
 * The mutation config is `polly.mutate.ts` in the cwd, else the first
 * Stryker config `findStrykerConfigs` discovers, read through the migration
 * mapping (deprecated: `polly mutate migrate --write` converts it). Paths
 * inside a config resolve against its directory; CLI flags resolve against
 * the cwd.
 */
import { existsSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { findStrykerConfigs } from "../../test/src/coverage-policy/mutate-targets.ts";
import type { MutateArgs } from "./args.ts";
import { loadMutationConfig, MUTATION_CONFIG_FILE, type MutationConfig } from "./define.ts";
import { readStrykerConfig } from "./migrate.ts";

const DEFAULT_REPORT = "reports/mutation/mutation.json";
const DEFAULT_DECISIONS = ".polly/test-debt/decisions.jsonl";

export interface LoadedMutationConfig {
  path: string;
  /** "stryker": read from a Stryker JSON through the migration mapping (deprecated). */
  format: "polly" | "stryker";
  config: MutationConfig;
  /** Migration notes (stryker format only). */
  notes: string[];
}

export interface MutateConfig {
  cwd: string;
  /** The config the bun engine runs from. Null if none was found or it failed to load. */
  mutation: LoadedMutationConfig | null;
  /** Why a Stryker config found as the fallback could not be mapped (fatal only when the engine runs). */
  mutationError: string | null;
  /** mutation-testing-report-schema JSON the analysis reads. */
  reportPath: string;
  /** Intermediate SQLite db (":memory:" by default; a path persists it). */
  dbPath: string;
  /** Version-controlled human-verdict log. */
  decisionsPath: string;
}

async function loadAt(path: string): Promise<LoadedMutationConfig> {
  if (path.endsWith(".json")) {
    const { config, notes } = await readStrykerConfig(path);
    return { path, format: "stryker", config, notes };
  }
  return { path, format: "polly", config: await loadMutationConfig(path), notes: [] };
}

export async function resolveMutateConfig(cwd: string, args: MutateArgs): Promise<MutateConfig> {
  const explicit = args.config ? resolve(cwd, args.config) : null;
  // findStrykerConfigs returns sorted absolute paths; the root stryker.conf.json
  // sorts before any stryker/ shard, so [0] is the root config when present.
  const discoveredStryker = (await findStrykerConfigs(cwd))[0] ?? null;

  const local = resolve(cwd, MUTATION_CONFIG_FILE);
  const mutationPath = explicit ?? (existsSync(local) ? local : discoveredStryker);
  let mutation: LoadedMutationConfig | null = null;
  let mutationError: string | null = null;
  if (mutationPath?.endsWith(".json")) {
    // A Stryker config the mapping cannot read (a jest runner, say) must not
    // block the report verbs, which need no config, so it is not fatal here.
    try {
      mutation = await loadAt(mutationPath);
    } catch (err) {
      mutationError = err instanceof Error ? err.message : String(err);
    }
  } else if (mutationPath) {
    mutation = await loadAt(mutationPath);
  }

  const base = mutation ? dirname(mutation.path) : cwd;
  const fromConfig = (flag: string | undefined, key: string | undefined, fallback: string) =>
    flag ? resolve(cwd, flag) : resolve(base, key ?? fallback);
  return {
    cwd,
    mutation,
    mutationError,
    reportPath: fromConfig(args.report, mutation?.config.report, DEFAULT_REPORT),
    dbPath: args.db ? resolve(cwd, args.db) : ":memory:",
    decisionsPath: fromConfig(args.decisions, mutation?.config.decisions, DEFAULT_DECISIONS),
  };
}
