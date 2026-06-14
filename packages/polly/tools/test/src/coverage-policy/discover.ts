/**
 * @fairfox/polly/test/coverage — zero-config loading.
 *
 * `polly coverage` runs without any config: it looks for a `coverage.config.ts`
 * (or `.js`) at the project root, and if there is none it returns an empty
 * config, which the engine treats as report-only — it prints the numbers and
 * the orphan count but never fails the build. A consumer opts into enforcement
 * by adding a `defaultThreshold`, and into legible tiering by adding `exempt`
 * entries. This mirrors how `polly test --tier` discovers tiers by convention.
 */

import { existsSync } from "node:fs";
import { isAbsolute, join, resolve } from "node:path";
import type { CoverageConfig } from "./types";

export interface LoadedConfig {
  config: CoverageConfig;
  /** Absolute path the config was loaded from, or null for the zero-config default. */
  source: string | null;
}

function isCoverageConfig(value: unknown): value is CoverageConfig {
  return typeof value === "object" && value !== null;
}

async function importConfig(path: string): Promise<CoverageConfig> {
  const mod: Record<string, unknown> = await import(path);
  const candidate = mod["config"] ?? mod["default"];
  if (!isCoverageConfig(candidate)) {
    throw new Error(`${path} must export \`config\` (a CoverageConfig object)`);
  }
  return candidate;
}

/**
 * Resolve the coverage config. With `explicitPath` (Polly's own front-end
 * passes scripts/coverage.config.ts) that file must exist. Otherwise look for
 * coverage.config.{ts,js} at the root; absent → the zero-config report-only
 * default.
 */
export async function loadCoverageConfig(
  root: string,
  explicitPath?: string
): Promise<LoadedConfig> {
  if (explicitPath) {
    const abs = isAbsolute(explicitPath) ? explicitPath : resolve(root, explicitPath);
    if (!existsSync(abs)) throw new Error(`coverage config not found: ${abs}`);
    return { config: await importConfig(abs), source: abs };
  }

  for (const name of ["coverage.config.ts", "coverage.config.js"]) {
    const abs = join(root, name);
    if (existsSync(abs)) return { config: await importConfig(abs), source: abs };
  }
  return { config: {}, source: null };
}
