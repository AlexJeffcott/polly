/**
 * Import-graph checks for `pollyCorePlugin`:
 *
 *   - polly:relative-imports — ban `../` imports beyond a depth threshold (#84)
 *   - polly:tsconfig-paths   — ban `compilerOptions.paths` aliases (#84)
 *   - polly:no-raw-http      — force HTTP through a canonical client (#86)
 *   - polly:types            — multi-package tsc --noEmit orchestrator (#85)
 *
 * All four are parameterised. Defaults are silent or zero-impact unless a
 * consumer opts in via `polly.config.ts`. Polly's own pre-commit pipeline
 * does not currently run these — they exist primarily for downstream
 * consumers (lingua, fairfox, warehouse-experiments) and ship under the
 * core plugin namespace so adoption is one config-block change away.
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

function isAllowedByGlob(rel: string, globs: string[]): boolean {
  for (const g of globs) {
    if (new Glob(g).match(rel)) return true;
  }
  return false;
}

const IMPORT_REGEX =
  /(?:import|export)\s+.*?from\s+['"]([^'"]+)['"]|require\(\s*['"]([^'"]+)['"]\s*\)/g;

function specifiersInLine(line: string): string[] {
  const out: string[] = [];
  IMPORT_REGEX.lastIndex = 0;
  let match = IMPORT_REGEX.exec(line);
  while (match !== null) {
    const s = match[1] || match[2];
    if (s) out.push(s);
    match = IMPORT_REGEX.exec(line);
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────
// polly:relative-imports — ban deep `../` imports
// ─────────────────────────────────────────────────────────────────

type RelativeImportsConfig = {
  /** Maximum depth of `../` traversal allowed; default 1. */
  maxDepth?: number;
  allowedFiles?: string[];
  zones?: string[];
  skipDirs?: string[];
};

const DEFAULT_RELATIVE: Required<RelativeImportsConfig> = {
  maxDepth: 1,
  allowedFiles: [],
  zones: ["src", "tools", "cli", "scripts"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

function relativeDepth(specifier: string): number {
  if (!specifier.startsWith("..")) return 0;
  let depth = 0;
  for (const segment of specifier.split("/")) {
    if (segment === "..") depth++;
    else break;
  }
  return depth;
}

async function scanFileForRelativeViolations(
  filePath: string,
  rel: string,
  maxDepth: number
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    if (isCommentLine(line.trim())) continue;
    for (const specifier of specifiersInLine(line)) {
      if (relativeDepth(specifier) > maxDepth) {
        out.push(`${rel}:${i + 1}: import "${specifier}" exceeds maxDepth ${maxDepth}`);
      }
    }
  }
  return out;
}

const relativeImports: Check<RelativeImportsConfig | undefined> = {
  id: "polly:relative-imports",
  description: "Ban `../` imports deeper than a configured threshold",
  filesRead: async (cfg, root) => {
    const c = cfg ?? {};
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_RELATIVE.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_RELATIVE.allowedFiles;
    const out: string[] = [];
    for (const z of c.zones ?? DEFAULT_RELATIVE.zones) {
      await walkScannableFiles(join(root, z), skipDirs, out);
    }
    return out.filter((p) => {
      const rel = relative(root, p);
      return !isTestFile(rel) && !isAllowedByGlob(rel, allowed);
    });
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const maxDepth = c.maxDepth ?? DEFAULT_RELATIVE.maxDepth;
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_RELATIVE.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_RELATIVE.allowedFiles;
    const violations: string[] = [];
    for (const z of c.zones ?? DEFAULT_RELATIVE.zones) {
      const files: string[] = [];
      await walkScannableFiles(join(rootDir, z), skipDirs, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isTestFile(rel) || isAllowedByGlob(rel, allowed)) continue;
        violations.push(...(await scanFileForRelativeViolations(filePath, rel, maxDepth)));
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:tsconfig-paths — ban `compilerOptions.paths` aliases
// ─────────────────────────────────────────────────────────────────

type TsconfigPathsConfig = {
  /** Filenames to scan; defaults to tsconfig.json variants. */
  files?: string[];
  /** Allowed alias patterns to keep (e.g. ["@/*"] for opt-in alias use). */
  allowedAliases?: string[];
};

const DEFAULT_TSCONFIG_PATHS: Required<TsconfigPathsConfig> = {
  files: ["tsconfig.json", "tsconfig.base.json"],
  allowedAliases: [],
};

async function findTsconfigs(rootDir: string, names: string[]): Promise<string[]> {
  const out: string[] = [];
  const skipDirs = new Set(SKIP_DIRS_DEFAULT);
  async function walk(dir: string): Promise<void> {
    let entries: import("node:fs").Dirent[];
    try {
      entries = await readdir(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      const fullPath = join(dir, entry.name);
      if (entry.isDirectory()) {
        if (!skipDirs.has(entry.name)) await walk(fullPath);
      } else if (entry.isFile() && names.includes(entry.name)) {
        out.push(fullPath);
      }
    }
  }
  await walk(rootDir);
  return out;
}

const tsconfigPaths: Check<TsconfigPathsConfig | undefined> = {
  id: "polly:tsconfig-paths",
  description: "Flag `compilerOptions.paths` entries (use package.json subpath imports instead)",
  filesRead: async (cfg, root) => findTsconfigs(root, cfg?.files ?? DEFAULT_TSCONFIG_PATHS.files),
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    const files = c.files ?? DEFAULT_TSCONFIG_PATHS.files;
    const allowed = new Set(c.allowedAliases ?? DEFAULT_TSCONFIG_PATHS.allowedAliases);
    const violations: string[] = [];
    for (const tsconfigPath of await findTsconfigs(rootDir, files)) {
      const raw = await Bun.file(tsconfigPath).text();
      const stripped = raw.replace(/\/\/[^\n]*\n/g, "\n").replace(/\/\*[\s\S]*?\*\//g, "");
      let parsed: { compilerOptions?: { paths?: Record<string, unknown> } };
      try {
        parsed = JSON.parse(stripped) as unknown as {
          compilerOptions?: { paths?: Record<string, unknown> };
        };
      } catch {
        violations.push(`${relative(rootDir, tsconfigPath)}: failed to parse as JSON`);
        continue;
      }
      const paths = parsed.compilerOptions?.paths ?? {};
      for (const alias of Object.keys(paths)) {
        if (allowed.has(alias)) continue;
        violations.push(`${relative(rootDir, tsconfigPath)}: paths["${alias}"] is set`);
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:no-raw-http — force HTTP through a canonical client
// ─────────────────────────────────────────────────────────────────

type NoRawHttpConfig = {
  /** Specifier for the canonical client (e.g. `#src/api/client`). Required. */
  canonicalClient?: string;
  banned?: string[];
  allowedFiles?: string[];
  zones?: string[];
  skipDirs?: string[];
};

const DEFAULT_NO_RAW_HTTP: Omit<Required<NoRawHttpConfig>, "canonicalClient"> = {
  banned: ["fetch", "XMLHttpRequest", "axios"],
  allowedFiles: [],
  zones: ["src"],
  skipDirs: SKIP_DIRS_DEFAULT,
};

function buildBannedCallRegex(banned: string[]): RegExp {
  const alts = banned.map((s) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|");
  // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp
  return new RegExp(`\\b(${alts})\\s*[\\(.]`);
}

async function scanFileForRawHttp(
  filePath: string,
  rel: string,
  canonicalClient: string,
  bannedRegex: RegExp
): Promise<string[]> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");
  const out: string[] = [];
  // The canonical-client implementation file legitimately uses the banned
  // identifiers — that's where the wrapping happens. We detect it
  // structurally by checking for an `export ... from "<canonicalClient>"`
  // re-export line. A simple substring test is enough; the canonical
  // client is a fixed module specifier the consumer configured, not an
  // arbitrary regex.
  const isCanonicalImpl = lines.some(
    (l) => l.includes(`from "${canonicalClient}"`) || l.includes(`from '${canonicalClient}'`)
  );
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] ?? "";
    const trimmed = line.trim();
    if (isCommentLine(trimmed)) continue;
    if (bannedRegex.test(line) && !isCanonicalImpl) {
      out.push(`${rel}:${i + 1}: ${trimmed}`);
    }
  }
  return out;
}

const noRawHttp: Check<NoRawHttpConfig | undefined> = {
  id: "polly:no-raw-http",
  description: "Force HTTP calls through a configured canonical client (opt-in)",
  filesRead: async (cfg, root) => {
    if (!cfg?.canonicalClient) return [];
    const skipDirs = new Set(cfg.skipDirs ?? DEFAULT_NO_RAW_HTTP.skipDirs);
    const allowed = cfg.allowedFiles ?? DEFAULT_NO_RAW_HTTP.allowedFiles;
    const out: string[] = [];
    for (const z of cfg.zones ?? DEFAULT_NO_RAW_HTTP.zones) {
      await walkScannableFiles(join(root, z), skipDirs, out);
    }
    return out.filter((p) => {
      const rel = relative(root, p);
      return !isTestFile(rel) && !isAllowedByGlob(rel, allowed);
    });
  },
  run: async ({ rootDir, config }) => {
    const c = config ?? {};
    if (!c.canonicalClient) {
      // No canonical client configured: rule is no-op. The umbrella's
      // "fail loud" stance applies when the user has half-configured it,
      // not when they haven't engaged with the rule at all.
      return { ok: true, messages: [] };
    }
    const banned = c.banned ?? DEFAULT_NO_RAW_HTTP.banned;
    const skipDirs = new Set(c.skipDirs ?? DEFAULT_NO_RAW_HTTP.skipDirs);
    const allowed = c.allowedFiles ?? DEFAULT_NO_RAW_HTTP.allowedFiles;
    const bannedRegex = buildBannedCallRegex(banned);
    const violations: string[] = [];
    for (const z of c.zones ?? DEFAULT_NO_RAW_HTTP.zones) {
      const files: string[] = [];
      await walkScannableFiles(join(rootDir, z), skipDirs, files);
      for (const filePath of files) {
        const rel = relative(rootDir, filePath);
        if (isTestFile(rel) || isAllowedByGlob(rel, allowed)) continue;
        violations.push(
          ...(await scanFileForRawHttp(filePath, rel, c.canonicalClient, bannedRegex))
        );
      }
    }
    return { ok: violations.length === 0, messages: violations };
  },
};

// ─────────────────────────────────────────────────────────────────
// polly:types — multi-package tsc --noEmit orchestrator
// ─────────────────────────────────────────────────────────────────

type TypesConfig = {
  /** Workspace globs to discover packages. */
  workspaces?: string[];
  /** Concurrency cap; defaults to os.cpus().length capped at workspace count. */
  concurrency?: number;
};

async function runTscFor(
  packagePath: string,
  rootDir: string
): Promise<{ ok: boolean; output: string }> {
  const proc = Bun.spawn(["bunx", "tsc", "--noEmit", "-p", packagePath], {
    cwd: rootDir,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  return { ok: proc.exitCode === 0, output: `${stdout}${stderr}` };
}

async function findWorkspaces(rootDir: string, patterns: string[]): Promise<string[]> {
  const out: string[] = [];
  for (const pattern of patterns) {
    const glob = new Glob(`${pattern}/tsconfig.json`);
    for await (const file of glob.scan({ cwd: rootDir, absolute: true })) {
      // Trim the trailing /tsconfig.json to get the package directory.
      out.push(file.replace(/\/tsconfig\.json$/, ""));
    }
  }
  return [...new Set(out)];
}

const types: Check<TypesConfig | undefined> = {
  id: "polly:types",
  description: "Run `tsc --noEmit` against each workspace package in parallel",
  filesRead: async () => {
    // The TypeScript compiler walks the entire dependency graph from
    // tsconfig.json out, which is far wider than what we can easily
    // declare here. We keep filesRead empty so the cache always misses
    // for this check; tsc has its own incremental cache and that is the
    // right place for that complexity to live.
    return [];
  },
  run: async ({ rootDir, config }) => {
    const patterns = (config ?? {}).workspaces ?? ["packages/*", "."];
    const packages = await findWorkspaces(rootDir, patterns);
    if (packages.length === 0) return { ok: true, messages: ["no workspace packages found"] };
    const results = await Promise.all(packages.map((p) => runTscFor(p, rootDir)));
    return aggregateTypesResults(packages, results, rootDir);
  },
};

function appendTscFailure(messages: string[], relPkg: string, output: string): void {
  messages.push(`${relPkg}: tsc --noEmit failed`);
  const trimmed = output.trim();
  if (!trimmed) return;
  for (const ln of trimmed.split("\n").slice(0, 30)) messages.push(`  ${ln}`);
}

function aggregateTypesResults(
  packages: string[],
  results: Array<{ ok: boolean; output: string }>,
  rootDir: string
): { ok: boolean; messages: string[] } {
  const messages: string[] = [];
  let ok = true;
  for (let i = 0; i < packages.length; i++) {
    const pkg = packages[i];
    const r = results[i];
    if (!pkg || !r || r.ok) continue;
    ok = false;
    appendTscFailure(messages, relative(rootDir, pkg) || ".", r.output);
  }
  return { ok, messages };
}

export const importCoreChecks: Check<unknown>[] = [
  relativeImports as Check<unknown>,
  tsconfigPaths as Check<unknown>,
  noRawHttp as Check<unknown>,
  types as Check<unknown>,
];
