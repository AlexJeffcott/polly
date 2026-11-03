/**
 * @fairfox/polly/test/coverage — mutation target / test-glob validation.
 *
 * A mutation config's target and test lists are hand-curated. A path that is
 * renamed, or a glob whose directory moves, silently resolves to nothing —
 * fewer files (or none) are mutated and the only signal is a long mutation
 * run whose score quietly drops. This asserts, in milliseconds, that every
 * entry still resolves to at least one file.
 *
 * Reads `polly.mutate.ts` at the root.
 */

import { existsSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { Glob } from "bun";
import { loadMutationConfig, MUTATION_CONFIG_FILE } from "../../../mutate/src/define.ts";

export interface MutateTargetIssue {
  config: string;
  field: "targets" | "tests.include";
  pattern: string;
}

/** One mutation config, reduced to the paths it names. */
export interface MutateConfigEntry {
  path: string;
  targets: { field: MutateTargetIssue["field"]; patterns: string[] };
  tests: { field: MutateTargetIssue["field"]; patterns: string[] };
}

export interface MutateTargetReport {
  configs: string[];
  issues: MutateTargetIssue[];
}

/** The mutation config under `root`, if any, with the paths it names. */
export async function findMutateConfigs(root: string): Promise<MutateConfigEntry[]> {
  const out: MutateConfigEntry[] = [];
  const polly = join(root, MUTATION_CONFIG_FILE);
  if (existsSync(polly)) {
    const config = await loadMutationConfig(polly);
    out.push({
      path: polly,
      targets: { field: "targets", patterns: config.targets },
      tests: { field: "tests.include", patterns: config.tests?.include ?? [] },
    });
  }
  return out;
}

function isGlob(pattern: string): boolean {
  return pattern.includes("*") || pattern.includes("?") || pattern.includes("[");
}

/** `file.ts:10-20` (or `:10:1-20:5`) names `file.ts`. */
const LINE_RANGE = /:\d+(?::\d+)?-\d+(?::\d+)?$/;

async function resolvesToFile(entry: string, cwd: string): Promise<boolean> {
  if (entry.startsWith("!")) return true; // negations are filters, not targets
  const pattern = entry.replace(LINE_RANGE, "");
  if (!isGlob(pattern)) return existsSync(resolve(cwd, pattern));
  const glob = new Glob(pattern);
  for await (const _ of glob.scan({ cwd, onlyFiles: true })) return true;
  return false;
}

async function checkField(
  configPath: string,
  field: MutateTargetIssue["field"],
  patterns: string[],
  cwd: string
): Promise<MutateTargetIssue[]> {
  const issues: MutateTargetIssue[] = [];
  for (const pattern of patterns) {
    if (!(await resolvesToFile(pattern, cwd))) {
      issues.push({ config: configPath, field, pattern });
    }
  }
  return issues;
}

/** Validate the mutation config under `root`. Its paths are relative to its own directory. */
export async function validateMutateTargets(root: string): Promise<MutateTargetReport> {
  const configs = await findMutateConfigs(root);
  const issues: MutateTargetIssue[] = [];
  for (const c of configs) {
    const cwd = dirname(c.path);
    issues.push(...(await checkField(c.path, c.targets.field, c.targets.patterns, cwd)));
    issues.push(...(await checkField(c.path, c.tests.field, c.tests.patterns, cwd)));
  }
  return { configs: configs.map((c) => c.path), issues };
}
