#!/usr/bin/env bun

/**
 * CLI wrapper for the no-tautology-ensures conformance check.
 *
 * The check logic lives in tools/quality/src/no-tautology-ensures.ts and
 * is exported from @fairfox/polly/quality so consuming applications can
 * import and run it programmatically. This script is the thin CLI entry
 * point for running it against the Polly codebase itself.
 *
 *   bun scripts/check-no-tautology-ensures.ts
 */

import { checkNoTautologyEnsures } from "../tools/quality/src/no-tautology-ensures";

const result = await checkNoTautologyEnsures({
  rootDir: process.cwd(),
  exclude: ["node_modules", "dist", ".git", ".bun", "coverage", "specs", "examples", "tests"],
});

result.print();
process.exit(result.violations.length > 0 ? 1 : 0);
