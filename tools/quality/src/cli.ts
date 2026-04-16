#!/usr/bin/env bun

/**
 * CLI entry point for Polly quality checks.
 *
 *   polly quality [--root <dir>] [--exclude <dirs>] [--pattern <glob>]
 *                 [--exclude-packages <names>] [--exclude-files <names>]
 *
 * Runs all conformance checks (currently: no-as-casting) against the
 * target directory and exits non-zero when violations are found.
 */

import { checkNoAsCasting } from "./no-as-casting";

const args = process.argv.slice(2);

function getFlag(name: string): string | undefined {
  const idx = args.indexOf(`--${name}`);
  return idx >= 0 ? args[idx + 1] : undefined;
}

const rootDir = getFlag("root") ?? process.cwd();
const exclude = getFlag("exclude")?.split(",") ?? ["node_modules", "dist", ".git", ".bun"];
const excludePackages = getFlag("exclude-packages")?.split(",");
const excludeFiles = getFlag("exclude-files")?.split(",");
const filePatterns = getFlag("pattern");

const result = await checkNoAsCasting({
  rootDir,
  exclude,
  ...(excludePackages ? { excludePackages } : {}),
  ...(excludeFiles ? { excludeFiles } : {}),
  ...(filePatterns ? { filePatterns } : {}),
});

result.print();
process.exit(result.violations.length > 0 ? 1 : 0);
