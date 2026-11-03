/**
 * Resolve the config and paths `polly mutate` works with.
 *
 * The mutation config is `polly.mutate.ts` in the cwd, or the file `--config`
 * names. Paths inside a config resolve against its directory; CLI flags
 * resolve against the cwd.
 */
import { existsSync } from "node:fs";
import { dirname, resolve } from "node:path";
import type { MutateArgs } from "./args.ts";
import { loadMutationConfig, MUTATION_CONFIG_FILE, type MutationConfig } from "./define.ts";

const DEFAULT_REPORT = "reports/mutation/mutation.json";
const DEFAULT_DECISIONS = ".polly/test-debt/decisions.jsonl";

export interface LoadedMutationConfig {
  path: string;
  config: MutationConfig;
}

export interface MutateConfig {
  cwd: string;
  /** The config the bun engine runs from. Null if none was found. */
  mutation: LoadedMutationConfig | null;
  /** mutation-testing-report-schema JSON the analysis reads. */
  reportPath: string;
  /** Intermediate SQLite db (":memory:" by default; a path persists it). */
  dbPath: string;
  /** Version-controlled human-verdict log. */
  decisionsPath: string;
}

export async function resolveMutateConfig(cwd: string, args: MutateArgs): Promise<MutateConfig> {
  const local = resolve(cwd, MUTATION_CONFIG_FILE);
  const mutationPath = args.config ? resolve(cwd, args.config) : existsSync(local) ? local : null;
  const mutation: LoadedMutationConfig | null = mutationPath
    ? { path: mutationPath, config: await loadMutationConfig(mutationPath) }
    : null;

  const base = mutation ? dirname(mutation.path) : cwd;
  const fromConfig = (flag: string | undefined, key: string | undefined, fallback: string) =>
    flag ? resolve(cwd, flag) : resolve(base, key ?? fallback);
  return {
    cwd,
    mutation,
    reportPath: fromConfig(args.report, mutation?.config.report, DEFAULT_REPORT),
    dbPath: args.db ? resolve(cwd, args.db) : ":memory:",
    decisionsPath: fromConfig(args.decisions, mutation?.config.decisions, DEFAULT_DECISIONS),
  };
}
