#!/usr/bin/env bun

/**
 * MODULE BOUNDARY ENFORCEMENT
 *
 * Polly's published library code lives in `src/`. Tooling lives in `tools/`
 * (verify, test, quality, analysis, visualize). The CLI binary lives in
 * `cli/`. Dev scripts live in `scripts/`.
 *
 * The boundary rules:
 *   - `src/` — published library — must NOT import from `tools/`, `cli/`,
 *     or `scripts/`. Otherwise consumers of @fairfox/polly would silently
 *     pull in dev tooling.
 *   - `tools/` — dev / authoring tools — may import from `src/` and
 *     sibling tools, but NOT from `cli/` or `scripts/`.
 *   - `cli/` — the polly bin — may import from anywhere internal.
 *   - `scripts/` — local dev scripts — may import from anywhere.
 *   - Workspace deps: any import via the package's own name
 *     (`@fairfox/polly/...`) must reach a real export, not a private
 *     internal path.
 *
 * Test files are excluded.
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";

interface Violation {
  file: string;
  line: number;
  content: string;
  rule: string;
}

const violations: Violation[] = [];
const rootDir = process.cwd();

const directionalBans: Record<string, string[]> = {
  src: ["tools/", "cli/", "scripts/"],
  tools: ["cli/", "scripts/"],
};

function getZone(filePath: string): string | null {
  const rel = relative(rootDir, filePath);
  for (const zone of ["src", "tools", "cli", "scripts"]) {
    if (rel === zone || rel.startsWith(`${zone}/`)) {
      return zone;
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

function resolveTargetZone(specifier: string, fromFile: string): string | null {
  // Only relative imports are zone-checkable.
  if (!specifier.startsWith(".") && !specifier.startsWith("/")) {
    return null;
  }
  const fromDir = relative(rootDir, fromFile).split("/").slice(0, -1).join("/");
  // Resolve `..` and `.` segments against the from-file's directory.
  const segments = `${fromDir}/${specifier}`.split("/");
  const resolved: string[] = [];
  for (const seg of segments) {
    if (seg === "" || seg === ".") {
      continue;
    }
    if (seg === "..") {
      resolved.pop();
      continue;
    }
    resolved.push(seg);
  }
  return resolved.join("/");
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

function recordImportViolations(
  specifier: string,
  filePath: string,
  fromZone: string,
  bans: readonly string[],
  ctx: { relPath: string; lineNumber: number; trimmed: string }
): void {
  const target = resolveTargetZone(specifier, filePath);
  if (!target) {
    return;
  }
  for (const banned of bans) {
    if (target.startsWith(banned)) {
      violations.push({
        file: ctx.relPath,
        line: ctx.lineNumber,
        content: ctx.trimmed,
        rule: `"${fromZone}/" cannot import from "${banned}" (resolved: ${target})`,
      });
    }
  }
}

function scanLine(
  line: string,
  filePath: string,
  fromZone: string,
  bans: readonly string[],
  relPath: string,
  lineNumber: number
): void {
  const trimmed = line.trim();
  if (isCommentLine(trimmed)) {
    return;
  }
  importRegex.lastIndex = 0;
  let match = importRegex.exec(line);
  while (match !== null) {
    const specifier = match[1] || match[2];
    if (specifier) {
      recordImportViolations(specifier, filePath, fromZone, bans, {
        relPath,
        lineNumber,
        trimmed,
      });
    }
    match = importRegex.exec(line);
  }
}

async function scanFile(filePath: string): Promise<void> {
  const fromZone = getZone(filePath);
  if (!fromZone) {
    return;
  }
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const bans = directionalBans[fromZone] ?? [];
  const relPath = relative(rootDir, filePath);

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line) {
      scanLine(line, filePath, fromZone, bans, relPath, i + 1);
    }
  }
}

for (const dir of ["src", "tools", "cli", "scripts"]) {
  await scanDirectory(join(rootDir, dir));
}

if (violations.length === 0) {
  process.stdout.write("✅ Module boundaries respected\n");
  process.exit(0);
}

process.stderr.write(`❌ ${violations.length} boundary violation(s):\n\n`);
for (const v of violations) {
  process.stderr.write(`  ${v.file}:${v.line}\n    ${v.content}\n    ${v.rule}\n\n`);
}
process.exit(1);
