#!/usr/bin/env bun

/**
 * Polly's front-end over the shipped mutate-target validator
 * (`@fairfox/polly/test/coverage` → validateMutateTargets). Polly's
 * polly.mutate.ts (and the deprecated stryker.conf.json) live at the monorepo
 * root, one level above this package, so we walk up to it and validate from there.
 *
 * Asserts every target and test glob in every mutation config still
 * resolves to a file — a renamed path silently drops out of the mutation
 * matrix otherwise, surfacing only in a ~45-minute run. See the engine for the
 * full rationale.
 */

import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { validateMutateTargets } from "../tools/test/src/coverage-policy/mutate-targets";

const MARKERS = ["polly.mutate.ts", "stryker.conf.json", "stryker"];

/** Nearest ancestor of cwd (inclusive) holding a mutation config. */
function configRoot(): string | null {
  let dir = process.cwd();
  while (!MARKERS.some((m) => existsSync(join(dir, m)))) {
    const parent = dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
  return dir;
}

const root = configRoot();
if (root === null) {
  process.stdout.write("⏩ No mutation config found — skipping mutate-target check\n");
  process.exit(0);
}

const report = await validateMutateTargets(root);

if (report.issues.length === 0) {
  process.stdout.write(
    `✅ All mutation targets and test globs resolve (${report.configs.length} config(s))\n`
  );
  process.exit(0);
}

process.stderr.write(`❌ ${report.issues.length} mutation target(s) resolve to no files:\n`);
for (const issue of report.issues) {
  process.stderr.write(`   ${issue.config} [${issue.field}] ${issue.pattern}\n`);
}
process.stderr.write("   A renamed/moved path silently drops out of the mutation matrix.\n");
process.exit(1);
