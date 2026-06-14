/**
 * @fairfox/polly/test/coverage — Stryker mutate-/test-target validation.
 *
 * A Stryker config's `mutate` and `testFiles` lists are hand-curated. A path
 * that is renamed, or a glob whose directory moves, silently resolves to
 * nothing — Stryker mutates fewer files (or none) and the only signal is a
 * long mutation run whose score quietly drops. This asserts, in milliseconds,
 * that every entry still resolves to at least one file.
 *
 * Discovers configs two ways, covering both layouts in the wild: a single
 * `stryker.conf.json` at the root, and a `stryker/` directory of per-package
 * shards.
 */

import { existsSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { Glob } from "bun";

interface StrykerConfig {
  mutate?: string[];
  testFiles?: string[];
  bun?: { testFiles?: string[] };
}

export interface MutateTargetIssue {
  config: string;
  field: "mutate" | "testFiles";
  pattern: string;
}

export interface MutateTargetReport {
  configs: string[];
  issues: MutateTargetIssue[];
}

/** Locate every Stryker config under the project root. */
export async function findStrykerConfigs(root: string): Promise<string[]> {
  const found: string[] = [];
  const single = join(root, "stryker.conf.json");
  if (existsSync(single)) found.push(single);

  const glob = new Glob("stryker/*.{json,conf.json}");
  for await (const rel of glob.scan({ cwd: root, onlyFiles: true })) {
    found.push(join(root, rel));
  }
  return found.sort();
}

function isGlob(pattern: string): boolean {
  return pattern.includes("*") || pattern.includes("?") || pattern.includes("[");
}

async function resolvesToFile(pattern: string, cwd: string): Promise<boolean> {
  if (pattern.startsWith("!")) return true; // negations are filters, not targets
  if (!isGlob(pattern)) return existsSync(resolve(cwd, pattern));
  const glob = new Glob(pattern);
  for await (const _ of glob.scan({ cwd, onlyFiles: true })) return true;
  return false;
}

async function checkField(
  configPath: string,
  field: "mutate" | "testFiles",
  patterns: string[] | undefined,
  cwd: string
): Promise<MutateTargetIssue[]> {
  const issues: MutateTargetIssue[] = [];
  for (const pattern of patterns ?? []) {
    if (!(await resolvesToFile(pattern, cwd))) {
      issues.push({ config: configPath, field, pattern });
    }
  }
  return issues;
}

/**
 * Validate every Stryker config under `root`. Paths in a Stryker config are
 * relative to that config's directory; for the monorepo-root configs that is
 * the root, so we resolve globs against `root`.
 */
export async function validateMutateTargets(root: string): Promise<MutateTargetReport> {
  const configs = await findStrykerConfigs(root);
  const issues: MutateTargetIssue[] = [];
  for (const configPath of configs) {
    const config = JSON.parse(readFileSync(configPath, "utf8")) as unknown as StrykerConfig;
    const testFiles = config.testFiles ?? config.bun?.testFiles;
    issues.push(...(await checkField(configPath, "mutate", config.mutate, root)));
    issues.push(...(await checkField(configPath, "testFiles", testFiles, root)));
  }
  return { configs, issues };
}
