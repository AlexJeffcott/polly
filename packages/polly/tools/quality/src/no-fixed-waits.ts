/**
 * No-fixed-waits conformance check.
 *
 * Bans fixed-duration sleeps: `page.waitForTimeout(n)`, `Bun.sleep(n)`, and a
 * `setTimeout` wrapped in a promise purely to resolve it. A fixed sleep encodes
 * an assumption about how fast the machine is — it passes on an idle machine
 * and fails on a loaded one, which is the root cause of flaky tests. Wait on a
 * real condition instead (a poll loop, a web-first assertion, a microtask
 * flush), or use the project's one sanctioned delay primitive where the wait
 * itself is the behaviour (rate-limit backoff, deliberate pacing).
 *
 * A plain `setTimeout(realCallback, n)` — a debounce, a throttle, a recursive
 * poll step — is NOT flagged; only the promise-resolving shape is the
 * anti-pattern. Point `excludeFiles` at the modules that define the blessed
 * delay/poll primitives (they necessarily contain a `setTimeout`).
 *
 * Exported from `@fairfox/polly/quality` so consumers run it programmatically;
 * polly registers it as the `polly:no-fixed-waits` plugin check. Ported from
 * the rule lingua and fairfox each maintained independently.
 */

import { readFileSync } from "node:fs";
import { Glob } from "bun";
import { logger } from "./logger";

export interface FixedWaitViolation {
  file: string;
  line: number;
  content: string;
  message: string;
}

export interface NoFixedWaitsResult {
  violations: FixedWaitViolation[];
  print: () => void;
}

export interface NoFixedWaitsOptions {
  rootDir: string;
  /** Directory names skipped anywhere in the path. */
  exclude?: string[];
  /**
   * Path suffixes skipped entirely — point these at the blessed delay/poll
   * primitives (e.g. `src/utils/poll.ts`) which legitimately call setTimeout.
   */
  excludeFiles?: string[];
  /** Glob of files to scan. Defaults to `**\/*.{ts,tsx}`. */
  filePatterns?: string;
}

const HINT =
  "wait on a real condition (poll loop, web-first assertion, microtask flush) or a sanctioned delay primitive";

const RULES: Array<{ pattern: RegExp; message: string }> = [
  { pattern: /\.waitForTimeout\s*\(/, message: `waitForTimeout is a fixed sleep — ${HINT}` },
  { pattern: /\bBun\.sleep\s*\(/, message: `Bun.sleep is a fixed sleep — ${HINT}` },
  {
    pattern: /\bsetTimeout\s*\(\s*(?:resolve|r|res|done)\s*,/,
    message: `setTimeout resolving a promise is a fixed sleep — ${HINT}`,
  },
  {
    pattern: /\bsetTimeout\s*\(\s*\(\s*\)\s*=>\s*(?:resolve|r|res|done)\b/,
    message: `setTimeout resolving a promise is a fixed sleep — ${HINT}`,
  },
  {
    pattern: /new\s+Promise\b.*\(\s*\(?\s*([A-Za-z_$][\w$]*)\s*\)?\s*=>.*\bsetTimeout\s*\(\s*\1\b/,
    message: `Promise wrapping setTimeout is a fixed sleep — ${HINT}`,
  },
];

const DEFAULT_EXCLUDE = ["node_modules", "dist", ".git", ".bun", "build", "coverage"];

/** Advance past a string literal opened at `i`; returns the closing-quote index. */
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

/**
 * Reduce a line to its executable code: string literal bodies are blanked and
 * any trailing `// …` comment is dropped. Keeps a banned pattern that only
 * appears inside a doc string or a comment from being flagged.
 */
function codeOnly(line: string): string {
  let out = "";
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '"' || ch === "'" || ch === "`") {
      const end = skipString(line, i);
      out += " ".repeat(end - i + 1);
      i = end;
      continue;
    }
    if (ch === "/" && line[i + 1] === "/") break;
    out += ch;
  }
  return out;
}

/**
 * Scan file text for fixed-wait violations. Exported so it can be unit-tested
 * directly without touching the filesystem.
 */
export function scanText(content: string, filePath = "<text>"): FixedWaitViolation[] {
  const violations: FixedWaitViolation[] = [];
  const lines = content.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    const trimmed = line.trim();
    if (
      trimmed === "" ||
      trimmed.startsWith("//") ||
      trimmed.startsWith("*") ||
      trimmed.startsWith("/*")
    ) {
      continue;
    }
    const code = codeOnly(line);
    const rule = RULES.find((r) => r.pattern.test(code));
    if (rule)
      violations.push({ file: filePath, line: i + 1, content: trimmed, message: rule.message });
  }
  return violations;
}

function isExcluded(relative: string, excludeDirs: Set<string>, excludeFiles: string[]): boolean {
  if (relative.split("/").some((s) => excludeDirs.has(s))) return true;
  const normalized = relative.replace(/\\/g, "/");
  return excludeFiles.some((suffix) => normalized.endsWith(suffix));
}

function printViolations(violations: FixedWaitViolation[]): void {
  if (violations.length === 0) {
    logger.log("[no-fixed-waits] ✅ No violations found.");
    return;
  }
  logger.log(`[no-fixed-waits] ❌ ${violations.length} fixed-duration wait(s) found:\n`);
  for (const v of violations) {
    logger.log(`  ${v.file}:${v.line}`);
    logger.log(`    ${v.content}`);
    logger.log(`    💡 ${v.message}`);
    logger.log("");
  }
}

/**
 * Run the no-fixed-waits check against a directory. Returns the violations
 * plus a `print` for CLI output, mirroring `checkNoAsCasting`.
 */
export async function checkNoFixedWaits(options: NoFixedWaitsOptions): Promise<NoFixedWaitsResult> {
  const { rootDir } = options;
  const excludeDirs = new Set(options.exclude ?? DEFAULT_EXCLUDE);
  const excludeFiles = [...(options.excludeFiles ?? []), "no-fixed-waits.ts"];
  const glob = new Glob(options.filePatterns ?? "**/*.{ts,tsx}");
  const violations: FixedWaitViolation[] = [];

  for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
    const relative = file.replace(`${rootDir}/`, "");
    if (isExcluded(relative, excludeDirs, excludeFiles)) continue;
    violations.push(...scanText(readFileSync(file, "utf-8"), relative));
  }

  return { violations, print: () => printViolations(violations) };
}
