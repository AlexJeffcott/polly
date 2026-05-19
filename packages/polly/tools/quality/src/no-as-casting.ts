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
import { logger } from "./logger";

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
  excludePackages?: string[];
  excludeFiles?: string[];
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

  // Full-line comments
  if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) {
    return true;
  }

  // as const (literal narrowing)
  if (line.match(/\bas const\b/)) {
    const withoutAsConst = line.replace(/\bas const\b/g, "");
    if (!withoutAsConst.includes(" as ")) return true;
  }

  // as unknown as (explicit escape hatch)
  if (line.includes(" as unknown as ") || line.trimEnd().endsWith("as unknown as")) {
    const withoutEscapeHatch = line.replace(/\bas unknown as\b/g, "");
    if (!withoutEscapeHatch.includes(" as ")) return true;
  }

  // Import/export renames
  if (
    line.match(/\b(import|export)\s+.*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+\*\s+as\s+\w+/) ||
    line.match(/\b(import|export)\s+type\s+.*\s+as\s+\w+/) ||
    line.match(/^\s*\w+\s+as\s+\w+,?\s*$/) ||
    line.match(/^\s*type\s+\w+\s+as\s+\w+,?\s*$/)
  ) {
    return true;
  }

  // Property declarations: as= or as: or as,
  if (line.match(/\bas\s*[=:,]/)) return true;

  // String literal detection: count quotes before each ` as ` occurrence.
  // If any quote type has an odd count, the ` as ` is inside a string.
  if (everyAsInsideString(line)) return true;

  // JSX text: ` as ` between > and < with no code syntax around it
  if (isJsxText(trimmed)) return true;

  // Plain text heuristic: indented line with no code syntax characters
  // before ` as ` — catches multiline JSX text and template literal bodies.
  if (isPlainText(trimmed)) return true;

  // Inline comment: ` as ` appears only after //
  const commentIdx = line.indexOf("//");
  if (commentIdx >= 0 && line.indexOf(" as ", commentIdx) >= 0) {
    const beforeComment = line.substring(0, commentIdx);
    if (!beforeComment.includes(" as ")) return true;
  }

  // SQL alias: `) as column_name`
  if (line.match(/"\)\s+as\s+\w+"/)) return true;

  if (line.includes(" satisfies ")) return true;

  return false;
}

/**
 * Returns true when every ` as ` occurrence in the line falls inside a
 * string literal (single-quoted, double-quoted, or backtick).
 */
function everyAsInsideString(line: string): boolean {
  let searchFrom = 0;
  while (true) {
    const idx = line.indexOf(" as ", searchFrom);
    if (idx < 0) return true; // no more ` as ` to check
    const before = line.substring(0, idx);
    const singleQuotes = (before.match(/'/g) ?? []).length;
    const doubleQuotes = (before.match(/"/g) ?? []).length;
    const backticks = (before.match(/`/g) ?? []).length;
    if (singleQuotes % 2 === 0 && doubleQuotes % 2 === 0 && backticks % 2 === 0) {
      return false; // this ` as ` is outside any string
    }
    searchFrom = idx + 4;
  }
}

/**
 * Detects JSX text content — ` as ` appearing between > and < with no
 * code-like syntax around it (no braces, semicolons, equals signs).
 */
function isJsxText(trimmed: string): boolean {
  // Classic JSX text: starts after > or is plain text ending before <
  if (trimmed.match(/^[^{};=()]*\bas\b[^{};=()]*$/)) {
    // No code syntax at all — could be JSX text or template literal body.
    // Reject if it looks like a type assertion (word ` as ` TypeName pattern
    // where TypeName starts with uppercase, or is a known TS type).
    if (
      !trimmed.match(/\bas\s+[A-Z]\w*/) &&
      !trimmed.match(/\bas\s+(string|number|boolean|any|unknown|never)\b/)
    ) {
      return true;
    }
  }
  return false;
}

/**
 * Heuristic for plain text in template literals or JSX: the line has no
 * code-like characters before ` as ` — no `=`, `{`, `}`, `:`, `;`, `(`.
 */
function isPlainText(trimmed: string): boolean {
  const idx = trimmed.indexOf(" as ");
  if (idx < 0) return false;
  const before = trimmed.substring(0, idx);
  // If nothing before ` as ` looks like code, it's probably prose.
  return (
    !before.match(/[={}:;(]/) &&
    !before.match(/\b(const|let|var|type|interface|function|return|await)\b/)
  );
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

function isFileExcluded(
  relative: string,
  excludeDirs: Set<string>,
  excludePackages: Set<string>,
  excludeFiles: Set<string>
): boolean {
  const segments = relative.split("/");
  if (segments.some((s) => excludeDirs.has(s))) return true;
  if (excludePackages.size > 0 && segments.some((s) => excludePackages.has(s))) return true;
  const basename = segments[segments.length - 1] ?? "";
  return excludeFiles.has(basename) || excludeFiles.has(relative);
}

function findViolations(relative: string, content: string): Violation[] {
  const results: Violation[] = [];
  const lines = content.split("\n");
  let insideTemplate = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    const backticks = (line.match(/`/g) ?? []).length;
    const startedInTemplate = insideTemplate;
    if (backticks % 2 === 1) insideTemplate = !insideTemplate;

    // Line is entirely inside a multi-line template literal and has no
    // interpolation — treat as string content (e.g. SQL column aliases).
    if (startedInTemplate && backticks === 0 && !line.includes("${")) continue;

    if (!isLineClean(line)) {
      results.push({
        file: relative,
        line: i + 1,
        content: line.trim(),
        advice: suggestFix(line.trim()),
      });
    }
  }
  return results;
}

function printViolations(violations: Violation[]): void {
  if (violations.length === 0) {
    logger.log("[no-as-casting] ✅ No violations found.");
    return;
  }
  logger.log(`[no-as-casting] ❌ ${violations.length} violation(s) found:\n`);
  for (const v of violations) {
    logger.log(`  ${v.file}:${v.line}`);
    logger.log(`    ${v.content}`);
    if (v.advice) logger.log(`    💡 ${v.advice}`);
    logger.log("");
  }
  logger.log("[no-as-casting] Use type guards, validation, or fix the types at the source.");
  logger.log('[no-as-casting] Only "as const" and "as unknown as" are allowed.');
}

/**
 * Run the no-as-casting check against a directory. Returns a result
 * object with the violations and a print function for CLI output.
 */
export async function checkNoAsCasting(options: CheckOptions): Promise<CheckResult> {
  const rootDir = options.rootDir;
  const excludeDirs = new Set(options.exclude ?? ["node_modules", "dist", ".git", ".bun"]);
  const excludePackages = new Set(options.excludePackages ?? []);
  const excludeFiles = new Set(options.excludeFiles ?? []);
  const pattern = options.filePatterns ?? "**/*.{ts,tsx}";
  const glob = new Glob(pattern);
  const violations: Violation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    if (isFileExcluded(relative, excludeDirs, excludePackages, excludeFiles)) continue;
    const content = readFileSync(file, "utf-8");
    violations.push(...findViolations(relative, content));
  }

  return { violations, print: () => printViolations(violations) };
}
