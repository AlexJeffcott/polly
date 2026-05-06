/**
 * Three more checks bundled into `pollyCorePlugin`:
 *
 *   - polly:forbidden-deps     — import-graph ban list (#87)
 *   - polly:no-state-hooks     — ban useState/useReducer/useSignal (#99)
 *   - polly:typographic-quotes — opt-in straight-vs-curly enforcement (#88)
 *
 * Each check is parameterised: defaults match polly's own pre-commit
 * surface; consumers override via `polly.config.ts`. Test files are
 * excluded by default for the import-walking checks since mocks and
 * fixtures legitimately reference banned packages.
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";
import { Glob } from "bun";
import type { Check } from "../types";

const SKIP_DIRS_DEFAULT = ["node_modules", ".git", "dist", ".bun", ".cache"];

function isCommentLine(trimmed: string): boolean {
  return trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*");
}

function isTestFile(rel: string): boolean {
  return (
    rel.includes("__tests__") ||
    rel.includes(".test.") ||
    rel.includes(".spec.") ||
    rel.startsWith("tests/")
  );
}

async function walkScannableFiles(
  dir: string,
  skipDirs: Set<string>,
  out: string[]
): Promise<void> {
  let entries: import("node:fs").Dirent[];
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const fullPath = join(dir, entry.name);
    if (entry.isDirectory()) {
      if (!skipDirs.has(entry.name)) await walkScannableFiles(fullPath, skipDirs, out);
    } else if (entry.isFile() && (entry.name.endsWith(".ts") || entry.name.endsWith(".tsx"))) {
      out.push(fullPath);
    }
  }
}

// ─────────────────────────────────────────────────────────────────
// polly:forbidden-deps — import-graph ban list
// ─────────────────────────────────────────────────────────────────

type ForbiddenDepsConfig = {
  /** Map of category description → list of banned package prefixes. */
  banned?: Record<string, string[]>;
  /** Top-level zones to scan. */
  zones?: string[];
  /** Directories to skip. */
  skipDirs?: string[];
};

const DEFAULT_FORBIDDEN: Required<ForbiddenDepsConfig> = {
  banned: {
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
    "Deprecated HTTP libraries (use fetch)": [
      "request",
      "request-promise",
      "request-promise-native",
    ],
    "Date-handling libraries (use Date or built-ins)": ["moment", "moment-timezone"],
  },
  zones: ["src", "tools", "cli", "scripts"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

const IMPORT_REGEX =
  /(?:import|export)\s+.*?from\s+['"]([^'"]+)['"]|require\(\s*['"]([^'"]+)['"]\s*\)/g;

function lookupBanned(
  specifier: string,
  banned: Record<string, string[]>
): { category: string } | null {
  for (const [category, prefixes] of Object.entries(banned)) {
    for (const p of prefixes) {
      if (specifier === p || specifier.startsWith(`${p}/`)) return { category };
    }
  }
  return null;
}

function scanLineForBanned(
  line: string,
  banned: Record<string, string[]>,
  rel: string,
  lineNumber: number
): Array<{ file: string; line: number; content: string; category: string }> {
  const trimmed = line.trim();
  if (isCommentLine(trimmed)) return [];
  const out: Array<{ file: string; line: number; content: string; category: string }> = [];
  IMPORT_REGEX.lastIndex = 0;
  let match = IMPORT_REGEX.exec(line);
  while (match !== null) {
    const specifier = match[1] || match[2];
    const hit = specifier ? lookupBanned(specifier, banned) : null;
    if (hit) {
      out.push({ file: rel, line: lineNumber, content: trimmed, category: hit.category });
    }
    match = IMPORT_REGEX.exec(line);
  }
  return out;
}

async function scanFileForForbidden(
  filePath: string,
  rel: string,
  banned: Record<string, string[]>
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    for (const v of scanLineForBanned(lines[i] ?? "", banned, rel, i + 1)) {
      out.push(`[${v.category}] ${v.file}:${v.line}: ${v.content}`);
    }
  }
  return out;
}

const forbiddenDeps: Check<ForbiddenDepsConfig | undefined> = {
  id: "polly:forbidden-deps",
  description:
    "Ban imports from a configured list of packages (alternative tools, deprecated libs)",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_FORBIDDEN.skipDirs);
    const out: string[] = [];
    for (const z of c.zones ?? DEFAULT_FORBIDDEN.zones) {
      await walkScannableFiles(join(root, z), skipDirs, out);
    }
    return out.filter((p) => !isTestFile(relative(root, p)));
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const banned = c.banned ?? DEFAULT_FORBIDDEN.banned;
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_FORBIDDEN.skipDirs);
    const violations: string[] = [];
    for (const z of c.zones ?? DEFAULT_FORBIDDEN.zones) {
      const files: string[] = [];
      await walkScannableFiles(join(rootDir, z), skipDirs, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isTestFile(rel)) continue;
        violations.push(...(await scanFileForForbidden(filePath, rel, banned)));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:no-state-hooks — ban local-state hooks (signals-first)
// ─────────────────────────────────────────────────────────────────

type NoStateHooksConfig = {
  /** Hook names to ban; defaults match polly's signals-first stance. */
  banned?: string[];
  /** Glob (relative to rootDir) of files exempt from the rule. */
  allowedFiles?: string[];
  zones?: string[];
  skipDirs?: string[];
};

const DEFAULT_NO_STATE_HOOKS: Required<NoStateHooksConfig> = {
  banned: ["useState", "useReducer", "useSignal"],
  allowedFiles: [],
  zones: ["src", "tools", "cli", "scripts"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

function escapeForAlternation(name: string): string {
  return name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function buildHookRegex(banned: string[]): RegExp {
  // Match either `import { useState[, …] } from …` or a call site `useState(`.
  const alts = banned.map(escapeForAlternation).join("|");
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp
  return new RegExp(`\\b(${alts})\\b`);
}

function isAllowedByGlob(rel: string, allowedFiles: string[]): boolean {
  for (const pattern of allowedFiles) {
    if (new Glob(pattern).match(rel)) return true;
  }
  return false;
}

const noStateHooks: Check<NoStateHooksConfig | undefined> = {
  id: "polly:no-state-hooks",
  description: "Ban useState/useReducer/useSignal — polly is signals-first",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_NO_STATE_HOOKS.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_NO_STATE_HOOKS.allowedFiles;
    const out: string[] = [];
    for (const z of c.zones ?? DEFAULT_NO_STATE_HOOKS.zones) {
      await walkScannableFiles(join(root, z), skipDirs, out);
    }
    return out.filter((p) => {
      const rel = relative(root, p);
      return !isTestFile(rel) && !isAllowedByGlob(rel, allowed);
    });
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const banned = c.banned ?? DEFAULT_NO_STATE_HOOKS.banned;
    if (banned.length === 0) return { ok: true, messages: [] };
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_NO_STATE_HOOKS.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_NO_STATE_HOOKS.allowedFiles;
    const regex = buildHookRegex(banned);
    const violations: string[] = [];
    for (const z of c.zones ?? DEFAULT_NO_STATE_HOOKS.zones) {
      const files: string[] = [];
      await walkScannableFiles(join(rootDir, z), skipDirs, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isTestFile(rel) || isAllowedByGlob(rel, allowed)) continue;
        violations.push(...(await scanFileForHookCalls(filePath, rel, regex)));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

async function scanFileForHookCalls(
  filePath: string,
  rel: string,
  regex: RegExp
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    if (isCommentLine(line.trim())) continue;
    if (regex.test(line)) out.push(`${rel}:${i + 1}: ${line.trim()}`);
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────
// polly:typographic-quotes — opt-in straight-vs-curly enforcement
// ─────────────────────────────────────────────────────────────────

type TypographicQuotesConfig = {
  /** Files matched by these globs must use typographic (curly) quotes. */
  typographicZone?: string[];
  /** Files matched by these globs must use straight quotes. */
  straightZone?: string[];
  zones?: string[];
  skipDirs?: string[];
};

const STRAIGHT_PATTERN = /["']/;
const TYPOGRAPHIC_PATTERN = /[‘’“”]/;

const DEFAULT_TYPOGRAPHIC: Required<TypographicQuotesConfig> = {
  // Empty defaults: the rule is no-op until a consumer configures zones.
  typographicZone: [],
  straightZone: [],
  zones: ["src", "tools", "cli", "scripts"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

function fileMatchesAnyGlob(rel: string, globs: string[]): boolean {
  for (const g of globs) {
    if (new Glob(g).match(rel)) return true;
  }
  return false;
}

const typographicQuotes: Check<TypographicQuotesConfig | undefined> = {
  id: "polly:typographic-quotes",
  description:
    "Enforce typographic quotes inside configured zones, straight quotes outside (opt-in)",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_TYPOGRAPHIC.skipDirs);
    const out: string[] = [];
    for (const z of c.zones ?? DEFAULT_TYPOGRAPHIC.zones) {
      await walkScannableFiles(join(root, z), skipDirs, out);
    }
    return out;
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const tz = c.typographicZone ?? DEFAULT_TYPOGRAPHIC.typographicZone;
    const sz = c.straightZone ?? DEFAULT_TYPOGRAPHIC.straightZone;
    if (tz.length === 0 && sz.length === 0) return { ok: true, messages: [] };
    return runTypographicScan(rootDir, c, tz, sz);
  },
};

async function scanFileForQuoteViolations(
  filePath: string,
  rel: string,
  inTypographicZone: boolean,
  inStraightZone: boolean
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    if (inTypographicZone && STRAIGHT_PATTERN.test(line)) {
      out.push(`${rel}:${i + 1}: straight quote in typographic zone — ${line.trim()}`);
    }
    if (inStraightZone && TYPOGRAPHIC_PATTERN.test(line)) {
      out.push(`${rel}:${i + 1}: typographic quote in straight zone — ${line.trim()}`);
    }
  }
  return out;
}

async function runTypographicScan(
  rootDir: string,
  c: TypographicQuotesConfig,
  tz: string[],
  sz: string[]
): Promise<{ ok: boolean; messages: string[] }> {
  const skipDirs = new Set(c.skipDirs ?? DEFAULT_TYPOGRAPHIC.skipDirs);
  const violations: string[] = [];
  for (const z of c.zones ?? DEFAULT_TYPOGRAPHIC.zones) {
    const files: string[] = [];
    await walkScannableFiles(join(rootDir, z), skipDirs, files);
    for (const filePath of files) {
      const rel = relative(rootDir, filePath);
      const inT = fileMatchesAnyGlob(rel, tz);
      const inS = fileMatchesAnyGlob(rel, sz);
      if (!inT && !inS) continue;
      violations.push(...(await scanFileForQuoteViolations(filePath, rel, inT, inS)));
    }
  }
  return { ok: violations.length === 0, messages: violations };
}

export const extraCoreChecks: Check<unknown>[] = [
  forbiddenDeps as Check<unknown>,
  noStateHooks as Check<unknown>,
  typographicQuotes as Check<unknown>,
];
