/**
 * No-require conformance check.
 *
 * Bans `require(...)` calls in TypeScript source. Inline CommonJS
 * escapes defeat bundler static analysis, hide cross-module
 * dependencies, and quietly opt a module out of ESM semantics that
 * the rest of the codebase depends on. The motivating incident was a
 * consumer app that shipped
 *
 *   const { renameSync } = require("node:fs") as typeof import("node:fs");
 *
 * wedged mid-function — the `as` cast alone violated no-as-casting,
 * but the underlying sin was the require call. Static ES imports
 * round-trip through every bundler and every IDE; `require` does
 * neither.
 *
 * Allowed: `import` / `export` syntax of any flavour, `import(...)`
 * dynamic imports (they're ESM), `require.resolve(...)` (sometimes
 * load-bearing for runtime path resolution), and occurrences inside
 * strings or comments.
 */

import { readFileSync } from "node:fs";
import { Glob } from "bun";
import { logger } from "./logger";

export interface NoRequireViolation {
  file: string;
  line: number;
  content: string;
}

export interface NoRequireCheckResult {
  violations: NoRequireViolation[];
  print: () => void;
}

export interface NoRequireCheckOptions {
  rootDir: string;
  exclude?: string[];
  /** Glob of files to scan. Defaults to `**` /`*.{ts,tsx}`. */
  filePatterns?: string;
}

/**
 * Returns true when the line contains no forbidden `require(` call.
 * Mirrors the shape of `isLineClean` in no-as-casting for
 * consistency; the two rules compose cleanly when both run against
 * the same file.
 */
export function isLineRequireClean(line: string): boolean {
  if (!line.includes("require")) {
    return true;
  }
  const trimmed = line.trim();
  if (
    trimmed.startsWith("//") ||
    trimmed.startsWith("*") ||
    trimmed.startsWith("/*")
  ) {
    return true;
  }
  const match = line.match(/\brequire\s*\(/);
  if (!match || match.index === undefined) {
    return true;
  }
  // Allow `require.resolve(...)` — a legitimate runtime-path helper
  // that preserves static analysis for the referenced module.
  if (line.slice(0, match.index + 8).endsWith("require.resolve(")) {
    return true;
  }
  // String literal detection: odd number of unescaped quotes before
  // the match means we're mid-string.
  const before = line.slice(0, match.index);
  const singles = (before.match(/(?<!\\)'/g) ?? []).length;
  const doubles = (before.match(/(?<!\\)"/g) ?? []).length;
  const backticks = (before.match(/(?<!\\)`/g) ?? []).length;
  if (singles % 2 === 1 || doubles % 2 === 1 || backticks % 2 === 1) {
    return true;
  }
  // Inline comment: `require(` appears only after `//`.
  const commentIdx = line.indexOf("//");
  if (commentIdx >= 0 && match.index > commentIdx) {
    return true;
  }
  return false;
}

function findRequireViolations(
  relative: string,
  content: string
): NoRequireViolation[] {
  const results: NoRequireViolation[] = [];
  const lines = content.split("\n");
  let insideTemplate = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    const backticks = (line.match(/`/g) ?? []).length;
    const startedInTemplate = insideTemplate;
    if (backticks % 2 === 1) {
      insideTemplate = !insideTemplate;
    }
    // Skip lines that are entirely inside a multi-line template
    // literal (e.g. an embedded code example in a doc comment).
    if (startedInTemplate && backticks === 0 && !line.includes("${")) {
      continue;
    }
    if (!isLineRequireClean(line)) {
      results.push({ file: relative, line: i + 1, content: line.trim() });
    }
  }
  return results;
}

function printRequireViolations(violations: NoRequireViolation[]): void {
  if (violations.length === 0) {
    logger.log("[no-require] ✅ No violations found.");
    return;
  }
  logger.log(`[no-require] ❌ ${violations.length} violation(s) found:\n`);
  for (const v of violations) {
    logger.log(`  ${v.file}:${v.line}`);
    logger.log(`    ${v.content}`);
    logger.log("");
  }
  logger.log(
    "[no-require] Replace with static ES imports or `await import(...)` for lazy ESM."
  );
}

export async function checkNoRequire(
  options: NoRequireCheckOptions
): Promise<NoRequireCheckResult> {
  const rootDir = options.rootDir;
  const excludeDirs = new Set(
    options.exclude ?? ["node_modules", "dist", ".git", ".bun"]
  );
  const pattern = options.filePatterns ?? "**/*.{ts,tsx}";
  const glob = new Glob(pattern);
  const violations: NoRequireViolation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    const segments = relative.split("/");
    if (segments.some((s) => excludeDirs.has(s))) {
      continue;
    }
    const content = readFileSync(file, "utf-8");
    violations.push(...findRequireViolations(relative, content));
  }

  return {
    violations,
    print: () => printRequireViolations(violations),
  };
}
