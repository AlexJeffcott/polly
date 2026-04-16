#!/usr/bin/env bun

/**
 * Conformance check: no TypeScript `as` type assertions.
 *
 * Adapted from lingua's scripts/check-no-as-casting.ts. Type assertions
 * bypass the type system rather than working with it. Code that needs an
 * assertion usually has a type bug that should be fixed at the source —
 * a missing generic parameter, a too-wide return type, or a function
 * that should return a discriminated union instead of a base type.
 *
 * Allowed patterns:
 *   - `as const` — literal type narrowing (safe, encouraged)
 *   - `as unknown as` — explicit escape hatch for impossible casts
 *   - import/export renames: `import { X as Y }`, `export { X as Y }`
 *   - `as` inside string literals (balanced quotes before the keyword)
 *   - `as` inside comments (after //)
 *   - `as` in property declarations: `as =`, `as:`, `as,`
 *
 * Everything else is a violation. Run with:
 *
 *   bun scripts/check-no-as-casting.ts
 *
 * Exits 0 if clean, 1 if violations found.
 *
 * Exportable: this check is also shipped as part of @fairfox/polly's
 * quality tooling so consuming applications can enforce the same rule.
 */

import { readFileSync } from "node:fs";
import { Glob } from "bun";

interface Violation {
  file: string;
  line: number;
  content: string;
}

const EXCLUDED_DIRS = new Set(["node_modules", "dist", ".git", ".bun", "examples"]);

/**
 * Check whether a line contains a forbidden `as` type assertion.
 * Returns true if the line is clean (no violation), false if it violates.
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Source-text scanning with many skip rules is inherently branchy.
export function isLineClean(line: string): boolean {
  // No ` as ` at all — trivially clean.
  if (!line.includes(" as ")) return true;

  const trimmed = line.trim();

  // Skip comments.
  if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) {
    return true;
  }

  // `as const` is safe.
  if (line.match(/\bas const\b/)) {
    // But only if EVERY ` as ` on this line is `as const`.
    const withoutAsConst = line.replace(/\bas const\b/g, "");
    if (!withoutAsConst.includes(" as ")) return true;
  }

  // `as unknown as` is the explicit escape hatch. Also allow it at end
  // of line for multiline casts where the target type is on the next line.
  if (line.includes(" as unknown as ") || line.trimEnd().endsWith("as unknown as")) {
    const withoutEscapeHatch = line.replace(/\bas unknown as\b/g, "");
    if (!withoutEscapeHatch.includes(" as ")) return true;
  }

  // Import/export renames.
  if (
    line.match(/\b(import|export)\s+.*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+\*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+type\s+.*\s+as\s+\w+/) ||
    line.match(/^\s*\w+\s+as\s+\w+,?\s*$/) ||
    line.match(/^\s*type\s+\w+\s+as\s+\w+,?\s*$/)
  ) {
    return true;
  }

  // Property declarations: `as =`, `as:`, `as,`.
  if (line.match(/\bas\s*[=:,]/)) {
    return true;
  }

  // SQL-style aliases: `) as column_name`.
  if (line.match(/\)\s+as\s+\w+/)) {
    return true;
  }

  // Inside a string literal: count quotes before ` as `.
  const idx = line.indexOf(" as ");
  if (idx >= 0) {
    const before = line.substring(0, idx);
    const singleQuotes = (before.match(/'/g) ?? []).length;
    const doubleQuotes = (before.match(/"/g) ?? []).length;
    const backticks = (before.match(/`/g) ?? []).length;
    if (singleQuotes % 2 === 1 || doubleQuotes % 2 === 1 || backticks % 2 === 1) {
      return true;
    }
  }

  // `as` after `//` on the same line (inline comment).
  const commentIdx = line.indexOf("//");
  if (commentIdx >= 0 && line.indexOf(" as ", commentIdx) >= 0) {
    const beforeComment = line.substring(0, commentIdx);
    if (!beforeComment.includes(" as ")) return true;
  }

  // `satisfies` keyword used alongside `as` in the same expression — skip
  // (biome sometimes rewrites satisfies chains that include `as`).
  if (line.includes(" satisfies ")) {
    return true;
  }

  return false;
}

/**
 * Suggest a concrete fix for a specific violation pattern. Returns a short
 * advice string, or undefined if no pattern-specific advice applies.
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Pattern-matching advice is a linear chain of if-returns.
function suggestFix(line: string): string | undefined {
  if (line.includes("JSON.parse")) {
    return "Use a validation function or type guard to parse and validate the result.";
  }
  if (
    line.includes("as HTMLInputElement") ||
    line.includes("as HTMLTextAreaElement") ||
    line.includes("as HTMLButtonElement")
  ) {
    return "Use instanceof: if (el instanceof HTMLInputElement) { el.value ... }";
  }
  if (line.includes("as HTMLElement") || line.includes("as Element")) {
    return "Use instanceof: if (el instanceof HTMLElement) { ... }";
  }
  if (line.includes(".doc()") && line.includes("as ")) {
    return "Type the DocHandle generic: repo.find<MyType>(id) returns DocHandle<MyType>.";
  }
  if (
    line.includes("Record<string, unknown>") &&
    (line.includes("window") || line.includes("globalThis"))
  ) {
    return "Extract a type guard: function getGlobalProp(name: string): unknown { ... }";
  }
  if (line.includes("Record<string, unknown>")) {
    return "Use a type guard function that narrows the unknown value to the target shape.";
  }
  if (line.includes("as PeerId") || line.includes("as DocumentId")) {
    return "Use the library's branded-type constructor if available, or centralise the cast in a factory.";
  }
  if (line.includes("as string") || line.includes("as number") || line.includes("as boolean")) {
    return "Narrow with typeof: if (typeof x === 'string') { ... }";
  }
  if (line.includes("as any")) {
    return "Replace 'any' with 'unknown' and add a type guard or validation at the boundary.";
  }
  return undefined;
}

async function main(): Promise<void> {
  const rootDir = process.cwd();
  const glob = new Glob("**/*.{ts,tsx}");
  const violations: Violation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    // Skip excluded directories (at any depth, not just root).
    const relative = file.replace(`${rootDir}/`, "");
    const segments = relative.split("/");
    if (segments.some((s) => EXCLUDED_DIRS.has(s))) continue;

    const content = readFileSync(file, "utf-8");
    const lines = content.split("\n");

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i] ?? "";
      if (!isLineClean(line)) {
        violations.push({
          file: relative,
          line: i + 1,
          content: line.trim(),
        });
      }
    }
  }

  if (violations.length === 0) {
    console.log("[no-as-casting] ✅ No violations found.");
    process.exit(0);
  }

  console.log(`[no-as-casting] ❌ ${violations.length} violation(s) found:\n`);
  for (const v of violations) {
    console.log(`  ${v.file}:${v.line}`);
    console.log(`    ${v.content}`);
    const advice = suggestFix(v.content);
    if (advice) {
      console.log(`    💡 ${advice}`);
    }
    console.log();
  }
  console.log("[no-as-casting] Use type guards, validation, or fix the types at the source.");
  console.log('[no-as-casting] Only "as const" and "as unknown as" are allowed.');
  process.exit(1);
}

if (import.meta.main) {
  main();
}
