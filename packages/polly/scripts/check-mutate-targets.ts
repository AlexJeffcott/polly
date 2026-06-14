#!/usr/bin/env bun

/**
 * Polly's front-end over the shipped mutate-target validator
 * (`@fairfox/polly/test/coverage` → validateMutateTargets). Polly's
 * stryker.conf.json lives at the monorepo root, one level above this package,
 * so we walk up to it and validate from there.
 *
 * Asserts every `mutate`/`testFiles` glob in every Stryker config still
 * resolves to a file — a renamed path silently drops out of the mutation
 * matrix otherwise, surfacing only in a ~45-minute run. See the engine for the
 * full rationale.
 */

import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { validateMutateTargets } from "../tools/test/src/coverage-policy/mutate-targets";

/** Nearest ancestor of cwd (inclusive) holding a Stryker config. */
function strykerRoot(): string | null {
  let dir = process.cwd();
  while (!existsSync(join(dir, "stryker.conf.json")) && !existsSync(join(dir, "stryker"))) {
    const parent = dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
  return dir;
}

const root = strykerRoot();
if (root === null) {
  process.stdout.write("⏩ No Stryker config found — skipping mutate-target check\n");
  process.exit(0);
}

const report = await validateMutateTargets(root);

if (report.issues.length === 0) {
  process.stdout.write(
    `✅ All Stryker mutate/testFiles targets resolve (${report.configs.length} config(s))\n`
  );
  process.exit(0);
}

process.stderr.write(`❌ ${report.issues.length} Stryker target(s) resolve to no files:\n`);
for (const issue of report.issues) {
  process.stderr.write(`   ${issue.config} [${issue.field}] ${issue.pattern}\n`);
}
process.stderr.write("   A renamed/moved path silently drops out of the mutation matrix.\n");
process.exit(1);
