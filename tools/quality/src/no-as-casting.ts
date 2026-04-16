/**
 * No-as-casting conformance check.
 *
 * Bans all TypeScript type assertions (`as Type`) except the allowed
 * patterns: `as const` (literal narrowing), `as unknown as` (explicit
 * escape hatch), import/export renames, and `as` inside strings or
 * comments. Violations include pattern-specific fix advice.
 *
 * This module exports the check logic as a library so consuming
 * applications can import it from `@fairfox/polly/quality` and run it
 * programmatically. Polly's own `scripts/check-no-as-casting.ts` is a
 * thin CLI wrapper around these exports.
 */

import { readFileSync } from "node:fs";
import { Glob } from "bun";

export interface Violation {
  file: string;
  line: number;
  content: string;
  advice?: string;
}

export interface CheckResult {
  violations: Violation[];
  print: () => void;
}

export interface CheckOptions {
  rootDir: string;
  exclude?: string[];
  filePatterns?: string;
}

/**
 * Check whether a line contains a forbidden `as` type assertion.
 * Returns true if the line is clean (no violation), false if it violates.
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Source-text scanning with many skip rules is inherently branchy.
export function isLineClean(line: string): boolean {
  if (!line.includes(" as ")) return true;

  const trimmed = line.trim();

  if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) {
    return true;
  }

  if (line.match(/\bas const\b/)) {
    const withoutAsConst = line.replace(/\bas const\b/g, "");
    if (!withoutAsConst.includes(" as ")) return true;
  }

  if (line.includes(" as unknown as ") || line.trimEnd().endsWith("as unknown as")) {
    const withoutEscapeHatch = line.replace(/\bas unknown as\b/g, "");
    if (!withoutEscapeHatch.includes(" as ")) return true;
  }

  if (
    line.match(/\b(import|export)\s+.*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+\*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+type\s+.*\s+as\s+\w+/) ||
    line.match(/^\s*\w+\s+as\s+\w+,?\s*$/) ||
    line.match(/^\s*type\s+\w+\s+as\s+\w+,?\s*$/)
  ) {
    return true;
  }

  if (line.match(/\bas\s*[=:,]/)) return true;
  if (line.match(/\)\s+as\s+\w+/)) return true;

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

  const commentIdx = line.indexOf("//");
  if (commentIdx >= 0 && line.indexOf(" as ", commentIdx) >= 0) {
    const beforeComment = line.substring(0, commentIdx);
    if (!beforeComment.includes(" as ")) return true;
  }

  if (line.includes(" satisfies ")) return true;

  return false;
}

/**
 * Suggest a concrete fix for a specific violation pattern.
 */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Pattern-matching advice is a linear chain of if-returns.
export function suggestFix(line: string): string | undefined {
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

/**
 * Run the no-as-casting check against a directory. Returns a result
 * object with the violations and a print function for CLI output.
 */
export async function checkNoAsCasting(options: CheckOptions): Promise<CheckResult> {
  const rootDir = options.rootDir;
  const excludeDirs = new Set(options.exclude ?? ["node_modules", "dist", ".git", ".bun"]);
  const pattern = options.filePatterns ?? "**/*.{ts,tsx}";
  const glob = new Glob(pattern);
  const violations: Violation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    const segments = relative.split("/");
    if (segments.some((s) => excludeDirs.has(s))) continue;

    const content = readFileSync(file, "utf-8");
    const lines = content.split("\n");

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i] ?? "";
      if (!isLineClean(line)) {
        violations.push({
          file: relative,
          line: i + 1,
          content: line.trim(),
          advice: suggestFix(line.trim()),
        });
      }
    }
  }

  return {
    violations,
    print() {
      if (violations.length === 0) {
        console.log("[no-as-casting] ✅ No violations found.");
        return;
      }
      console.log(`[no-as-casting] ❌ ${violations.length} violation(s) found:\n`);
      for (const v of violations) {
        console.log(`  ${v.file}:${v.line}`);
        console.log(`    ${v.content}`);
        if (v.advice) console.log(`    💡 ${v.advice}`);
        console.log();
      }
      console.log("[no-as-casting] Use type guards, validation, or fix the types at the source.");
      console.log('[no-as-casting] Only "as const" and "as unknown as" are allowed.');
    },
  };
}
