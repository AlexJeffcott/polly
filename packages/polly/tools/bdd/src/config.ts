/**
 * Resolve the feature files and step modules `polly bdd` operates on, relative
 * to the cwd it was invoked from — so a consumer's project tree works the same
 * as this repo. Convention (overridable with --features / --steps):
 *   - features:  features/**\/*.feature
 *   - steps:     features/**\/*.steps.ts  +  features/steps.ts
 * A positional path narrows the feature glob to a single file or directory.
 */
import { resolve } from "node:path";
import { Glob } from "bun";
import type { BddArgs } from "./args.ts";

export interface BddConfig {
  cwd: string;
  /** Absolute paths of `.feature` files to run. */
  featureFiles: string[];
  /** Absolute paths of step-definition modules to import (side-effect registration). */
  stepFiles: string[];
}

async function expand(cwd: string, pattern: string): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Glob(pattern).scan({ cwd, absolute: true, onlyFiles: true })) {
    out.push(f);
  }
  return out.sort();
}

export async function resolveBddConfig(cwd: string, args: BddArgs): Promise<BddConfig> {
  // A positional path (verb's first rest arg for `run`) narrows the features.
  const pathArg = args.verb === "run" ? args.rest[0] : undefined;

  let featurePattern = args.features ?? "features/**/*.feature";
  if (pathArg) {
    featurePattern = pathArg.endsWith(".feature")
      ? pathArg
      : `${pathArg.replace(/\/$/, "")}/**/*.feature`;
  }

  const stepPatterns = args.steps ? [args.steps] : ["features/**/*.steps.ts", "features/steps.ts"];

  const featureFiles = pathArg?.endsWith(".feature")
    ? [resolve(cwd, pathArg)]
    : await expand(cwd, featurePattern);

  const stepSets = await Promise.all(stepPatterns.map((p) => expand(cwd, p)));
  const stepFiles = [...new Set(stepSets.flat())];

  return { cwd, featureFiles, stepFiles };
}
