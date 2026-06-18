/**
 * No-tautology-ensures conformance check.
 *
 * Refuses `ensures(...)` / `requires(...)` calls whose predicate (the
 * first positional argument) is a tautology: a bare literal (`true`,
 * `false`, `null`, `undefined`, a number, a string) or a comparison of
 * two literals (`1 === 1`). These primitives are Polly's formal-verify
 * contracts — `ensures`/`requires` (and the wider verify family the
 * Stryker ignorer lists in `tools/verify/src/stryker`) compile away at
 * runtime and translate to TLA+ assertions under verification. A
 * tautological predicate therefore asserts nothing, yet reads in review
 * like a genuine safety check. Swapping a real predicate for `true`
 * looks like a refactor and silently disables the only guard on a
 * one-step handler; this lint stops that rewrite from merging.
 *
 * This module exports the check logic as a library so consuming
 * applications can import it from `@fairfox/polly/quality` and run it
 * programmatically. Polly's own `scripts/check-no-tautology-ensures.ts`
 * is a thin CLI wrapper around these exports.
 *
 * The scan is text-based, not AST-based: the only call sites are
 * `ensures(<expr>, '<message>')` / `requires(<expr>, '<message>')` with
 * the predicate as the first argument, so a balanced-paren walk that
 * skips string and comment content is sufficient and keeps the false
 * positive rate at zero.
 */

import { readFileSync } from "node:fs";
import { Glob } from "bun";
import { logger } from "./logger";

export interface TautologyViolation {
  file: string;
  line: number;
  content: string;
  reason: string;
}

export interface NoTautologyEnsuresResult {
  violations: TautologyViolation[];
  print: () => void;
}

export interface NoTautologyEnsuresOptions {
  rootDir: string;
  /** Directory names skipped anywhere in the path. */
  exclude?: string[];
  /** Basenames or relative paths skipped entirely. */
  excludeFiles?: string[];
  /** Glob of files to scan. Defaults to `**\/*.{ts,tsx}`. */
  filePatterns?: string;
  /**
   * Verify primitives whose first argument is a runtime-inert predicate.
   * Defaults to the predicate-taking pair `ensures` / `requires`; pass a
   * wider set (e.g. `invariant`, `stateConstraint`) to match a project's
   * own usage.
   */
  primitives?: string[];
}

const DEFAULT_PRIMITIVES = ["ensures", "requires"];
const DEFAULT_EXCLUDE = ["node_modules", "dist", ".git", ".bun", "coverage", "specs"];

const LITERAL = /^(true|false|null|undefined|\d+(\.\d+)?|"[^"]*"|'[^']*'|`[^`]*`)$/;

/**
 * Classify a predicate string. Returns the tautology reason, or
 * `undefined` when the predicate references state and is therefore a
 * real assertion. Conservative by design: only the explicit literal and
 * literal-vs-literal forms are flagged, so anything touching an
 * identifier or property access passes.
 */
export function tautologyReason(predicate: string): string | undefined {
  const trimmed = predicate.trim();
  if (LITERAL.test(trimmed)) return `literal '${trimmed}'`;

  const cmp = trimmed.match(/^(.+?)\s*(===|!==|==|!=)\s*(.+)$/);
  if (cmp) {
    const lhs = cmp[1]?.trim() ?? "";
    const rhs = cmp[3]?.trim() ?? "";
    if (LITERAL.test(lhs) && LITERAL.test(rhs)) return `literal-vs-literal '${trimmed}'`;
  }
  return undefined;
}

/**
 * If `text[i]` opens a string literal, return the index of its closing
 * quote (skipping escapes); otherwise return `i` unchanged. Lets the
 * paren/comma walkers treat string bodies as opaque without inlining the
 * scan logic at each call site.
 */
function skipString(text: string, i: number): number {
  const quote = text[i];
  if (quote !== '"' && quote !== "'" && quote !== "`") return i;
  let j = i + 1;
  while (j < text.length && text[j] !== quote) {
    if (text[j] === "\\") j++;
    j++;
  }
  return j;
}

/** Index of the `)` that closes the `(` at `openIdx`, skipping strings. */
function findClosingParen(text: string, openIdx: number): number {
  let depth = 0;
  for (let i = openIdx; i < text.length; i++) {
    const ch = text[i];
    if (ch === "(") {
      depth++;
    } else if (ch === ")") {
      if (--depth === 0) return i;
    } else {
      i = skipString(text, i);
    }
  }
  return -1;
}

/** Split a call's argument list on top-level commas, skipping strings/nesting. */
export function splitTopLevelArgs(args: string): string[] {
  const parts: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < args.length; i++) {
    const ch = args[i];
    if (ch === "(" || ch === "[" || ch === "{") {
      depth++;
    } else if (ch === ")" || ch === "]" || ch === "}") {
      depth--;
    } else if (ch === "," && depth === 0) {
      parts.push(args.slice(start, i));
      start = i + 1;
    } else {
      i = skipString(args, i);
    }
  }
  parts.push(args.slice(start));
  return parts.map((p) => p.trim());
}

function isFileExcluded(
  relative: string,
  excludeDirs: Set<string>,
  excludeFiles: Set<string>
): boolean {
  const segments = relative.split("/");
  if (segments.some((s) => excludeDirs.has(s))) return true;
  const basename = segments[segments.length - 1] ?? "";
  return excludeFiles.has(basename) || excludeFiles.has(relative);
}

/** True when a matched occurrence is an import/re-export or a comment, not a call. */
function isNonCall(line: string, lineBefore: string): boolean {
  const isImport = /\b(import|export)\b/.test(line) && line.includes("{") && !line.includes(";");
  const isFrom = /\b(import|export)\b.*\bfrom\b/.test(line);
  return isImport || isFrom || lineBefore.includes("//");
}

function findViolations(
  relative: string,
  content: string,
  callPattern: RegExp
): TautologyViolation[] {
  const results: TautologyViolation[] = [];
  callPattern.lastIndex = 0;
  let match: RegExpExecArray | null = callPattern.exec(content);
  while (match !== null) {
    const current = match;
    match = callPattern.exec(content);

    const openIdx = current.index + current[0].length - 1;
    const lineStart = content.lastIndexOf("\n", current.index) + 1;
    const lineEnd = content.indexOf("\n", current.index);
    const line = content.slice(lineStart, lineEnd === -1 ? content.length : lineEnd);
    if (isNonCall(line, content.slice(lineStart, current.index))) continue;

    const closeIdx = findClosingParen(content, openIdx);
    if (closeIdx === -1) continue;
    const predicate = splitTopLevelArgs(content.slice(openIdx + 1, closeIdx))[0];
    const reason = predicate ? tautologyReason(predicate) : undefined;
    if (reason === undefined) continue;

    results.push({
      file: relative,
      line: content.slice(0, current.index).split("\n").length,
      content: line.trim(),
      reason: `${current[1] ?? "ensures"}(...) predicate is a ${reason}`,
    });
  }
  return results;
}

function printViolations(violations: TautologyViolation[]): void {
  if (violations.length === 0) {
    logger.log("[no-tautology-ensures] ✅ No violations found.");
    return;
  }
  logger.log(`[no-tautology-ensures] ❌ ${violations.length} violation(s) found:\n`);
  for (const v of violations) {
    logger.log(`  ${v.file}:${v.line}`);
    logger.log(`    ${v.content}`);
    logger.log(`    💡 ${v.reason}`);
    logger.log("");
  }
  logger.log(
    "[no-tautology-ensures] A verify predicate must reference state — a literal asserts nothing."
  );
}

/**
 * Run the no-tautology-ensures check against a directory. Returns the
 * violations plus a `print` for CLI output, mirroring `checkNoAsCasting`.
 */
export async function checkNoTautologyEnsures(
  options: NoTautologyEnsuresOptions
): Promise<NoTautologyEnsuresResult> {
  const { rootDir } = options;
  const excludeDirs = new Set(options.exclude ?? DEFAULT_EXCLUDE);
  const excludeFiles = new Set([...(options.excludeFiles ?? []), "no-tautology-ensures.ts"]);
  const primitives = options.primitives ?? DEFAULT_PRIMITIVES;
  const callPattern = new RegExp(`\\b(${primitives.join("|")})\\s*\\(`, "g");
  const glob = new Glob(options.filePatterns ?? "**/*.{ts,tsx}");
  const violations: TautologyViolation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    if (isFileExcluded(relative, excludeDirs, excludeFiles)) continue;
    violations.push(...findViolations(relative, readFileSync(file, "utf-8"), callPattern));
  }

  return { violations, print: () => printViolations(violations) };
}
