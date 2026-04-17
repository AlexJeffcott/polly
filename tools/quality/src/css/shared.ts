/**
 * Shared plumbing for CSS conformance checks.
 *
 * File discovery, violation printing, and common scanner options live
 * here so each check (`quality`, `layout`, `vars`, `unused`) can stay
 * focused on its own rule set.
 */

import type { Dirent } from "node:fs";
import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";
import { logger } from "../logger.ts";

export type CssViolation = {
  file: string;
  line: number;
  rule: string;
  content: string;
  suggestion: string;
};

export type CssCheckResult = {
  violations: CssViolation[];
  print: () => void;
};

export type CssScanOptions = {
  rootDir: string;
  /** Directory names (not paths) to skip during recursion. */
  skipDirs?: string[];
  /** File names (not paths) to skip entirely. */
  skipFiles?: string[];
};

export const DEFAULT_SKIP_DIRS = [
  "node_modules",
  ".git",
  "dist",
  "dist-test",
  "build",
  "coverage",
];

export async function walkDirectory(
  dir: string,
  visit: (filePath: string, relPath: string) => Promise<void>,
  opts: CssScanOptions,
): Promise<void> {
  const skipDirs = new Set(opts.skipDirs ?? DEFAULT_SKIP_DIRS);
  const skipFiles = new Set(opts.skipFiles ?? []);
  const rootDir = opts.rootDir;

  async function walk(current: string): Promise<void> {
    let entries: Dirent[];
    try {
      entries = await readdir(current, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      const full = join(current, entry.name);
      if (entry.isDirectory()) {
        if (skipDirs.has(entry.name)) continue;
        await walk(full);
      } else if (entry.isFile()) {
        if (skipFiles.has(entry.name)) continue;
        const rel = relative(rootDir, full);
        await visit(full, rel);
      }
    }
  }

  await walk(dir);
}

export function formatViolations(
  kind: string,
  violations: CssViolation[],
  rootDir: string,
): string[] {
  const lines: string[] = [];
  if (violations.length === 0) {
    lines.push(`✅ ${kind}: no violations`);
    return lines;
  }
  lines.push(`❌ ${kind}: ${violations.length} violation(s)`);
  const byFile = new Map<string, CssViolation[]>();
  for (const v of violations) {
    const bucket = byFile.get(v.file) ?? [];
    bucket.push(v);
    byFile.set(v.file, bucket);
  }
  for (const [file, fileViolations] of byFile) {
    lines.push(`  ${relative(rootDir, file)}`);
    for (const v of fileViolations) {
      lines.push(`    L${v.line}: ${v.content}`);
      lines.push(`          → ${v.suggestion} [${v.rule}]`);
    }
  }
  return lines;
}

export function makeResult(kind: string, rootDir: string, violations: CssViolation[]): CssCheckResult {
  return {
    violations,
    print() {
      for (const line of formatViolations(kind, violations, rootDir)) {
        if (line.startsWith("❌")) {
          logger.error(line);
        } else {
          logger.log(line);
        }
      }
    },
  };
}

/** True when the line is a CSS comment (standalone or continuation). */
export function isInsideComment(line: string): boolean {
  const trimmed = line.trim();
  return (
    trimmed.startsWith("/*") ||
    trimmed.startsWith("*") ||
    trimmed.startsWith("//")
  );
}

/** Heuristic: true when the given line number falls inside an @keyframes block. */
export function isInsideKeyframes(
  lineNum: number,
  allLines: readonly string[],
): boolean {
  for (let i = lineNum - 1; i >= 0; i -= 1) {
    const l = allLines[i]?.trim() ?? "";
    if (l.startsWith("@keyframes")) return true;
    if (l === "}" && i < lineNum - 1) return false;
  }
  return false;
}
