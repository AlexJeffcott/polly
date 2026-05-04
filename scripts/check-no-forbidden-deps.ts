#!/usr/bin/env bun

/**
 * FORBIDDEN DEPENDENCY ENFORCEMENT
 *
 * Bans imports of packages that overlap with tooling already chosen for
 * this codebase. The goal is to keep the dependency graph small and
 * keep one team-wide answer to "how do we do X?".
 *
 * Test files are excluded (mocking may legitimately reference banned packages).
 * Examples are excluded (they're demo apps with their own dependency choices).
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";

interface Violation {
  file: string;
  line: number;
  content: string;
  category: string;
}

const violations: Violation[] = [];

const rootDir = process.cwd();

const bannedImports: Record<string, string[]> = {
  "Alternative test runners (we use bun:test)": [
    "vitest",
    "jest",
    "@jest/globals",
    "mocha",
    "ava",
    "tape",
    "tap",
    "uvu",
  ],
  "Alternative linters/formatters (we use biome)": [
    "eslint",
    "@eslint",
    "prettier",
    "@prettier",
    "tslint",
  ],
  "Deprecated HTTP libraries (use fetch)": ["request", "request-promise", "request-promise-native"],
  "Date-handling libraries (use Date or built-ins)": ["moment", "moment-timezone"],
};

const bannedLookup: Array<{ prefix: string; category: string }> = [];
for (const [category, modules] of Object.entries(bannedImports)) {
  for (const mod of modules) {
    bannedLookup.push({ prefix: mod, category });
  }
}

function isBannedImport(specifier: string): { category: string } | null {
  for (const { prefix, category } of bannedLookup) {
    if (specifier === prefix || specifier.startsWith(`${prefix}/`)) {
      return { category };
    }
  }
  return null;
}

const importRegex =
  /(?:import|export)\s+.*?from\s+['"]([^'"]+)['"]|require\(\s*['"]([^'"]+)['"]\s*\)/g;

function isTestFile(filePath: string): boolean {
  const rel = relative(rootDir, filePath);
  return (
    rel.includes("__tests__") ||
    rel.includes(".test.") ||
    rel.includes(".spec.") ||
    rel.startsWith("tests/")
  );
}

async function scanDirectory(dir: string): Promise<void> {
  let entries: import("node:fs").Dirent[];
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (
        entry.name === "node_modules" ||
        entry.name === ".git" ||
        entry.name === "dist" ||
        entry.name === ".bun" ||
        entry.name === ".cache"
      ) {
        continue;
      }
      await scanDirectory(fullPath);
    } else if (entry.isFile() && (entry.name.endsWith(".ts") || entry.name.endsWith(".tsx"))) {
      if (!isTestFile(fullPath)) {
        await scanFile(fullPath);
      }
    }
  }
}

function isCommentLine(trimmed: string): boolean {
  return trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*");
}

function collectLineViolations(line: string, relPath: string, lineNumber: number): void {
  const trimmed = line.trim();
  importRegex.lastIndex = 0;
  let match = importRegex.exec(line);
  while (match !== null) {
    const specifier = match[1] || match[2];
    const banned = specifier ? isBannedImport(specifier) : null;
    if (banned) {
      violations.push({
        file: relPath,
        line: lineNumber,
        content: trimmed,
        category: banned.category,
      });
    }
    match = importRegex.exec(line);
  }
}

async function scanFile(filePath: string): Promise<void> {
  const file = Bun.file(filePath);
  const content = await file.text();
  const lines = content.split("\n");
  const relPath = relative(rootDir, filePath);

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (!line || isCommentLine(line.trim())) {
      continue;
    }
    collectLineViolations(line, relPath, i + 1);
  }
}

// Scan polly's own source — not examples (each example has its own choices).
for (const dir of ["src", "tools", "cli", "scripts"]) {
  await scanDirectory(join(rootDir, dir));
}

if (violations.length === 0) {
  process.stdout.write("✅ No forbidden dependencies found\n");
  process.exit(0);
}

const grouped = new Map<string, Violation[]>();
for (const v of violations) {
  const list = grouped.get(v.category) ?? [];
  list.push(v);
  grouped.set(v.category, list);
}

process.stderr.write(`❌ ${violations.length} forbidden import(s):\n\n`);
for (const [category, categoryViolations] of grouped) {
  process.stderr.write(`  ${category}\n`);
  for (const v of categoryViolations) {
    process.stderr.write(`    ${v.file}:${v.line}\n      ${v.content}\n`);
  }
  process.stderr.write("\n");
}
process.exit(1);
