#!/usr/bin/env bun

/**
 * CLI wrapper for the no-require conformance check. The check logic
 * lives in tools/quality/src/no-require.ts and is exported from
 * @fairfox/polly/quality so consumer apps can import and run it
 * programmatically. This script is the thin CLI entry point for
 * running it against Polly's own codebase.
 *
 *   bun scripts/check-no-require.ts
 */

import { checkNoRequire } from "../tools/quality/src/no-require";

const result = await checkNoRequire({
  rootDir: process.cwd(),
  exclude: ["node_modules", "dist", ".git", ".bun", "examples"],
});

result.print();
process.exit(result.violations.length > 0 ? 1 : 0);
