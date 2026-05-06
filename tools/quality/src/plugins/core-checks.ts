/**
 * Additional checks bundled into `pollyCorePlugin`.
 *
 * Each check here is a port of an existing `scripts/check-*.ts` script
 * from polly's repo into the plugin contract. The original scripts
 * remain on disk for back-compat with the existing pre-commit
 * orchestrator (`scripts/check.ts`); the plugin path is the new way
 * for downstream consumers (lingua, fairfox, warehouse-experiments)
 * who do not want to copy the script verbatim.
 *
 * Out of scope for this release:
 *   - `polly:boundaries` issue text describes a workspace-dependency
 *     model (each package may only import from packages it lists in
 *     its `dependencies`). Polly itself is a single-package repo and
 *     uses directional zone bans (`src/` cannot import `tools/`,
 *     etc.); that model is what ships here. The workspace-dep model
 *     can be layered on as an additional configuration mode later.
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";
import type { Check } from "../types";

// ─────────────────────────────────────────────────────────────────
// polly:security — semgrep SAST wrapper
// ─────────────────────────────────────────────────────────────────

type SecurityConfig = {
  /** Override the semgrep ruleset; defaults to `auto`. */
  config?: string;
  /** Severity floors passed to `--severity`; defaults to ERROR + WARNING. */
  severities?: string[];
  /** Glob excludes appended after the severities. */
  exclude?: string[];
};

async function semgrepInstalled(): Promise<boolean> {
  const which = Bun.spawn(["which", "semgrep"], { stdout: "ignore", stderr: "ignore" });
  await which.exited;
  return which.exitCode === 0;
}

const security: Check<SecurityConfig | undefined> = {
  id: "polly:security",
  description: "Run `semgrep scan` against the working tree (SAST)",
  // semgrep walks the tree on disk; we use cacheKeyExtras to capture
  // the ruleset name so a config flip re-scans even on identical files.
  // filesRead is intentionally empty: the tree-walking surface is wider
  // than any glob we'd hand-write here, and semgrep's own incremental
  // model is what consumers should rely on inside CI. Cache invalidation
  // on tool version + ruleset is enough to make repeat invocations cheap.
  cacheKeyExtras: (cfg) => {
    const c = cfg ?? {};
    return {
      config: c.config ?? "auto",
      severities: (c.severities ?? ["ERROR", "WARNING"]).slice().sort().join(","),
      exclude: (c.exclude ?? []).slice().sort().join(","),
    };
  },
  run: async ({ rootDir, config }) => {
    if (!(await semgrepInstalled())) {
      return {
        ok: false,
        messages: [
          "semgrep is not on PATH. Install with `brew install semgrep` (macOS) or `pip install semgrep`.",
        ],
      };
    }
    const cfg = config ?? {};
    const args = ["semgrep", "scan", "--config", cfg.config ?? "auto", "--quiet", "--error"];
    for (const sev of cfg.severities ?? ["ERROR", "WARNING"]) {
      args.push("--severity", sev);
    }
    for (const exc of cfg.exclude ?? ["Dockerfile*", "docker-compose*"]) {
      args.push(`--exclude=${exc}`);
    }
    const proc = Bun.spawn(args, { cwd: rootDir, stdout: "pipe", stderr: "pipe" });
    const [stdout, stderr] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
    ]);
    await proc.exited;
    const output = `${stdout}${stderr}`.trim();
    return {
      ok: proc.exitCode === 0,
      messages: proc.exitCode === 0 ? [] : [output || `semgrep exited ${proc.exitCode}`],
    };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:boundaries — directional zone-ban import check
// ─────────────────────────────────────────────────────────────────

type BoundariesConfig = {
  /** From-zone → list of zone path prefixes that zone may not import from. */
  bans?: Record<string, string[]>;
  /** Zone names to scan; entries map to subdirectories of rootDir. */
  zones?: string[];
  /** Directories whose names cause a recursive scan to skip. */
  skipDirs?: string[];
};

const DEFAULT_BOUNDARIES: BoundariesConfig = {
  bans: { src: ["tools/", "cli/", "scripts/"], tools: ["cli/", "scripts/"] },
  zones: ["src", "tools", "cli", "scripts"],
  skipDirs: ["node_modules", ".git", "dist", ".bun", ".cache"],
};

const IMPORT_REGEX =
  /(?:import|export)\s+.*?from\s+['"]([^'"]+)['"]|require\(\s*['"]([^'"]+)['"]\s*\)/g;

function isTestFile(rel: string): boolean {
  return (
    rel.includes("__tests__") ||
    rel.includes(".test.") ||
    rel.includes(".spec.") ||
    rel.startsWith("tests/")
  );
}

function resolveTargetZone(specifier: string, fromFile: string, rootDir: string): string | null {
  if (!specifier.startsWith(".") && !specifier.startsWith("/")) return null;
  const fromDir = relative(rootDir, fromFile).split("/").slice(0, -1).join("/");
  const segments = `${fromDir}/${specifier}`.split("/");
  const resolved: string[] = [];
  for (const seg of segments) {
    if (seg === "" || seg === ".") continue;
    if (seg === "..") {
      resolved.pop();
      continue;
    }
    resolved.push(seg);
  }
  return resolved.join("/");
}

async function collectScannableFiles(
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
      if (!skipDirs.has(entry.name)) await collectScannableFiles(fullPath, skipDirs, out);
    } else if (entry.isFile() && (entry.name.endsWith(".ts") || entry.name.endsWith(".tsx"))) {
      out.push(fullPath);
    }
  }
}

function violationsForBoundarySpecifier(
  specifier: string,
  ctx: {
    filePath: string;
    rootDir: string;
    zone: string;
    bans: string[];
    rel: string;
    line: number;
  }
): Array<{ file: string; line: number; rule: string }> {
  const target = resolveTargetZone(specifier, ctx.filePath, ctx.rootDir);
  if (!target) return [];
  const out: Array<{ file: string; line: number; rule: string }> = [];
  for (const banned of ctx.bans) {
    if (target.startsWith(banned)) {
      out.push({
        file: ctx.rel,
        line: ctx.line,
        rule: `"${ctx.zone}/" cannot import from "${banned}" (resolved: ${target})`,
      });
    }
  }
  return out;
}

function scanLineForBoundary(
  line: string,
  ctx: {
    filePath: string;
    rootDir: string;
    zone: string;
    bans: string[];
    rel: string;
    lineNumber: number;
  }
): Array<{ file: string; line: number; rule: string }> {
  const trimmed = line.trim();
  if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) return [];
  const out: Array<{ file: string; line: number; rule: string }> = [];
  IMPORT_REGEX.lastIndex = 0;
  let match = IMPORT_REGEX.exec(line);
  while (match !== null) {
    const specifier = match[1] || match[2];
    if (specifier) {
      out.push(...violationsForBoundarySpecifier(specifier, { ...ctx, line: ctx.lineNumber }));
    }
    match = IMPORT_REGEX.exec(line);
  }
  return out;
}

function scanFileForBoundaryViolations(
  filePath: string,
  content: string,
  rootDir: string,
  zone: string,
  bans: string[]
): Array<{ file: string; line: number; rule: string }> {
  const rel = relative(rootDir, filePath);
  const lines = content.split("\n");
  const out: Array<{ file: string; line: number; rule: string }> = [];
  for (let i = 0; i < lines.length; i++) {
    out.push(
      ...scanLineForBoundary(lines[i] ?? "", {
        filePath,
        rootDir,
        zone,
        bans,
        rel,
        lineNumber: i + 1,
      })
    );
  }
  return out;
}

const boundaries: Check<BoundariesConfig | undefined> = {
  id: "polly:boundaries",
  description: "Enforce directional import bans between top-level zones (src/tools/cli/scripts)",
  filesRead: async (cfg, root) => {
    const c = { ...DEFAULT_BOUNDARIES, ...(cfg ?? {}) };
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_BOUNDARIES.skipDirs ?? []);
    const out: string[] = [];
    for (const zone of c.zones ?? DEFAULT_BOUNDARIES.zones ?? []) {
      await collectScannableFiles(join(root, zone), skipDirs, out);
    }
    return out.filter((p) => !isTestFile(relative(root, p)));
  },
  run: async ({ rootDir, config }) => {
    const c = { ...DEFAULT_BOUNDARIES, ...(config ?? {}) };
    const bans = c.bans ?? {};
    const zones = c.zones ?? [];
    const skipDirs = new Set(c.skipDirs ?? []);
    const all: Array<{ file: string; line: number; rule: string }> = [];
    for (const zone of zones) {
      const files: string[] = [];
      await collectScannableFiles(join(rootDir, zone), skipDirs, files);
      const fromBans = bans[zone] ?? [];
      if (fromBans.length === 0) continue;
      for (const filePath of files) {
        if (isTestFile(relative(rootDir, filePath))) continue;
        const content = await Bun.file(filePath).text();
        all.push(...scanFileForBoundaryViolations(filePath, content, rootDir, zone, fromBans));
      }
    }
    return {
      ok: all.length === 0,
      messages: all.map((v) => `${v.file}:${v.line}: ${v.rule}`),
    };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:server-imports — ban node:* / bun:* in browser packages
// ─────────────────────────────────────────────────────────────────

type ServerImportsConfig = {
  /** Path prefixes that are browser-targeting; their files cannot import banned specifiers. */
  browserPaths?: string[];
  /** Module specifiers that are server-only. */
  bannedSpecifiers?: string[];
  /** Files (relative to rootDir) excluded from the rule. */
  allowFiles?: string[];
  skipDirs?: string[];
};

const DEFAULT_SERVER_IMPORTS: Required<Omit<ServerImportsConfig, "allowFiles">> = {
  browserPaths: [
    "src/popup",
    "src/content",
    "src/devtools",
    "src/options",
    "src/offscreen",
    "src/page",
    "src/ui",
    "src/polly-ui",
    "tools/test/src/browser",
  ],
  bannedSpecifiers: [
    "bun:sqlite",
    "bun:ffi",
    "bun:jsc",
    "node:fs",
    "node:fs/promises",
    "node:path",
    "node:child_process",
    "node:net",
    "node:os",
    "node:http",
    "node:https",
    "node:stream",
    "node:worker_threads",
    "node:cluster",
    "node:tls",
    "node:dns",
    "better-sqlite3",
    "sqlite3",
    "ws",
  ],
  skipDirs: ["node_modules", "dist", ".cache"],
};

function buildBannedRegex(specs: string[]): RegExp {
  // Each specifier is regex-escaped so user-supplied names cannot inject
  // metacharacters into the compiled pattern. The output regex is a fixed
  // shape with the escaped alternation embedded; the only dynamic input is
  // the alternation list, and every entry has been quoted.
  const escaped = specs.map((s) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|");
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp
  return new RegExp(
    `(?:import|export)\\s+.*?from\\s+['"](?:${escaped})(?:/[^'"]*)?['"]|require\\(\\s*['"](?:${escaped})(?:/[^'"]*)?['"]\\s*\\)`
  );
}

function isExcludedFromServerCheck(rel: string, allow: Set<string>): boolean {
  if (allow.has(rel)) return true;
  return rel.includes("__tests__") || rel.includes(".test.") || rel.includes(".spec.");
}

function scanFileForServerImports(rel: string, content: string, bannedRegex: RegExp): string[] {
  const violations: string[] = [];
  const lines = content.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    const trimmed = line.trim();
    if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) continue;
    if (bannedRegex.test(line)) {
      violations.push(`${rel}:${i + 1}: ${trimmed}`);
    }
  }
  return violations;
}

const serverImports: Check<ServerImportsConfig | undefined> = {
  id: "polly:server-imports",
  description: "Ban node:* / bun:* imports inside browser-targeting packages",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_SERVER_IMPORTS.skipDirs);
    const allow = new Set(c.allowFiles ?? []);
    const out: string[] = [];
    for (const p of c.browserPaths ?? DEFAULT_SERVER_IMPORTS.browserPaths) {
      await collectScannableFiles(join(root, p), skipDirs, out);
    }
    return out.filter((p) => !isExcludedFromServerCheck(relative(root, p), allow));
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_SERVER_IMPORTS.skipDirs);
    const bannedRegex = buildBannedRegex(
      c.bannedSpecifiers ?? DEFAULT_SERVER_IMPORTS.bannedSpecifiers
    );
    const allow = new Set(c.allowFiles ?? []);
    const violations: string[] = [];
    for (const p of c.browserPaths ?? DEFAULT_SERVER_IMPORTS.browserPaths) {
      const files: string[] = [];
      await collectScannableFiles(join(rootDir, p), skipDirs, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isExcludedFromServerCheck(rel, allow)) continue;
        const content = await Bun.file(filePath).text();
        violations.push(...scanFileForServerImports(rel, content, bannedRegex));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

export const additionalCoreChecks: Check<unknown>[] = [
  security as Check<unknown>,
  boundaries as Check<unknown>,
  serverImports as Check<unknown>,
];
