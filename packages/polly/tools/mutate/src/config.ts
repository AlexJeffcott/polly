/**
 * Resolve the paths and Stryker config `polly mutate` works with. Everything is
 * resolved against the cwd the command was invoked from, so a consumer's project
 * tree works the same as this repo. Stryker-config discovery reuses the existing
 * `findStrykerConfigs` helper that `polly coverage` already depends on.
 */
import { resolve } from "node:path";
import { findStrykerConfigs } from "../../test/src/coverage-policy/mutate-targets.ts";
import type { MutateArgs } from "./args.ts";

const DEFAULT_REPORT = "reports/mutation/mutation.json";
const DEFAULT_DECISIONS = ".polly/test-debt/decisions.jsonl";

export interface MutateConfig {
  cwd: string;
  /** The Stryker config to use — explicit `--config`, else the first discovered. Null if none found. */
  strykerConfigPath: string | null;
  /** mutation-testing-report-schema JSON the analysis reads. */
  reportPath: string;
  /** Intermediate SQLite db (":memory:" by default; a path persists it). */
  dbPath: string;
  /** Version-controlled human-verdict log. */
  decisionsPath: string;
}

export async function resolveMutateConfig(cwd: string, args: MutateArgs): Promise<MutateConfig> {
  let strykerConfigPath: string | null = null;
  if (args.config) {
    strykerConfigPath = resolve(cwd, args.config);
  } else {
    // findStrykerConfigs returns sorted absolute paths; the root stryker.conf.json
    // sorts before any stryker/ shard, so [0] is the root config when present.
    const found = await findStrykerConfigs(cwd);
    strykerConfigPath = found[0] ?? null;
  }

  return {
    cwd,
    strykerConfigPath,
    reportPath: resolve(cwd, args.report ?? DEFAULT_REPORT),
    dbPath: args.db ? resolve(cwd, args.db) : ":memory:",
    decisionsPath: resolve(cwd, args.decisions ?? DEFAULT_DECISIONS),
  };
}
