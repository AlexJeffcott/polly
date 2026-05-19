#!/usr/bin/env bun

/**
 * CLI wrapper for the no-as-casting conformance check.
 *
 * The check logic lives in tools/quality/src/no-as-casting.ts and is
 * exported from @fairfox/polly/quality so consuming applications can
 * import and run it programmatically. This script is the thin CLI entry
 * point for running it against the Polly codebase itself.
 *
 *   bun scripts/check-no-as-casting.ts
 */

import { checkNoAsCasting } from "../tools/quality/src/no-as-casting";

const result = await checkNoAsCasting({
  rootDir: process.cwd(),
  exclude: ["node_modules", "dist", ".git", ".bun", "examples"],
});

result.print();
process.exit(result.violations.length > 0 ? 1 : 0);
