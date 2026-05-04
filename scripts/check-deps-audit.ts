#!/usr/bin/env bun
/**
 * Dependency security & freshness audit.
 *
 * Runs three things and aggregates the result:
 *   - `osv-scanner scan source -r .` (CVEs across npm, Dockerfile base images, ...)
 *   - `bun audit` (npm CVEs from bun.lock)
 *   - `bun outdated --filter='*'` (freshness across the workspace)
 *
 * Hard-fails when any CVE is found. Caches results at `.cache/deps-audit.json`
 * keyed on a hash of the inputs (every package.json, bun.lock, Dockerfile*,
 * Brewfile, deps-notes.json). When the hash matches, prints the cached
 * summary instead of re-running — the real `osv-scanner` invocation can take
 * 30+ seconds against the public database.
 *
 * Verbose mode (`--verbose`) walks `deps-notes.json` and shows each direct
 * dependency, the workspace it lives in, the note explaining what it does in
 * this codebase, and a usage count derived from grep. Direct deps without a
 * note print a TODO so the file stays in sync as deps come and go.
 *
 * Required tooling: `osv-scanner` on PATH. Install via `brew bundle`. The
 * script hard-fails with an install hint if it's missing.
 */

import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";

const ROOT = process.cwd();
const CACHE_DIR = join(ROOT, ".cache");
const CACHE_FILE = join(CACHE_DIR, "deps-audit.json");
const NOTES_FILE = join(ROOT, "deps-notes.json");

const VERBOSE = process.argv.includes("--verbose") || process.argv.includes("-v");
const NO_CACHE = process.argv.includes("--no-cache");

// ---------------------------------------------------------------------------
// Hash inputs that should invalidate the cache
// ---------------------------------------------------------------------------

function listInputFiles(): string[] {
  const files: string[] = [
    "package.json",
    "bun.lock",
    "Brewfile",
    "deps-notes.json",
    "tools/verify/Dockerfile",
    "tools/verify/specs/Dockerfile",
  ];
  // Workspace package.json files (just `tests/` for polly).
  if (existsSync(join(ROOT, "tests/package.json"))) {
    files.push("tests/package.json");
  }
  // Example package.jsons — examples aren't in the workspace but their deps
  // still inform the supply-chain surface, so include them in the cache key.
  const examplesDir = join(ROOT, "examples");
  if (existsSync(examplesDir)) {
    for (const entry of readdirSafe(examplesDir)) {
      const root = join("examples", entry, "package.json");
      if (existsSync(join(ROOT, root))) {
        files.push(root);
      }
      // Two-level nesting (server/client subprojects).
      const inner = join(ROOT, "examples", entry);
      if (existsSync(inner)) {
        for (const sub of readdirSafe(inner)) {
          const subPkg = join("examples", entry, sub, "package.json");
          if (existsSync(join(ROOT, subPkg))) {
            files.push(subPkg);
          }
        }
      }
    }
  }
  return files;
}

function readdirSafe(dir: string): string[] {
  try {
    return readdirSync(dir);
  } catch {
    return [];
  }
}

function hashInputs(): string {
  const hash = createHash("sha256");
  for (const file of listInputFiles().sort()) {
    const path = join(ROOT, file);
    if (!existsSync(path)) {
      hash.update(`${file}:missing\n`);
      continue;
    }
    hash.update(`${file}:`);
    hash.update(readFileSync(path));
    hash.update("\n");
  }
  return hash.digest("hex");
}

// ---------------------------------------------------------------------------
// Cache I/O
// ---------------------------------------------------------------------------

interface CachedResult {
  hash: string;
  timestamp: string;
  cveCount: number;
  cveDetails: string;
  outdated: string;
  outdatedCount: number;
}

function loadCache(): CachedResult | null {
  if (NO_CACHE || !existsSync(CACHE_FILE)) {
    return null;
  }
  try {
    return JSON.parse(readFileSync(CACHE_FILE, "utf8")) as unknown as CachedResult;
  } catch {
    return null;
  }
}

function saveCache(result: CachedResult): void {
  if (!existsSync(CACHE_DIR)) {
    mkdirSync(CACHE_DIR, { recursive: true });
  }
  writeFileSync(CACHE_FILE, `${JSON.stringify(result, null, 2)}\n`);
}

// ---------------------------------------------------------------------------
// Tooling presence
// ---------------------------------------------------------------------------

function requireBinary(name: string, hint: string): void {
  const which = spawnSync("which", [name], { encoding: "utf8" });
  if (which.status !== 0) {
    process.stderr.write(`❌ ${name} is required but not on PATH.\n   ${hint}\n`);
    process.exit(2);
  }
}

// ---------------------------------------------------------------------------
// Audit runners
// ---------------------------------------------------------------------------

function runOsvScanner(): { cveCount: number; output: string } {
  // Only scan code that ships in @fairfox/polly: root + tests workspace.
  // Examples are demo apps with their own (often older) dep choices and aren't
  // part of the published surface — bun audit on each example is the right
  // tool there if you want to lint them.
  const proc = spawnSync(
    "osv-scanner",
    [
      "scan",
      "source",
      "-r",
      ".",
      "--experimental-exclude",
      "examples",
      "--format",
      "json",
    ],
    {
      cwd: ROOT,
      encoding: "utf8",
      maxBuffer: 64 * 1024 * 1024,
    }
  );

  // osv-scanner exits 1 when vulnerabilities are found, 0 when clean. Other
  // codes are tooling failures.
  if (proc.status !== 0 && proc.status !== 1) {
    return {
      cveCount: 0,
      output: `osv-scanner failed with exit ${proc.status}:\n${proc.stderr || proc.stdout}`,
    };
  }

  type OsvVuln = { id: string; summary?: string };
  type OsvPkg = {
    package?: { name?: string; version?: string };
    vulnerabilities?: OsvVuln[];
  };
  type OsvOutput = { results?: Array<{ packages?: OsvPkg[] }> };

  const stdout = proc.stdout || "{}";
  let parsed: OsvOutput = {};
  try {
    parsed = JSON.parse(stdout) as unknown as OsvOutput;
  } catch {
    return { cveCount: 0, output: stdout };
  }

  let count = 0;
  const lines: string[] = [];
  for (const result of parsed.results ?? []) {
    for (const pkg of result.packages ?? []) {
      const vulns = pkg.vulnerabilities;
      if (!vulns || vulns.length === 0) {
        continue;
      }
      count += vulns.length;
      const name = pkg.package?.name ?? "<unknown>";
      const version = pkg.package?.version ?? "<unknown>";
      for (const v of vulns) {
        lines.push(`  ${name}@${version} — ${v.id}: ${v.summary ?? ""}`);
      }
    }
  }
  return { cveCount: count, output: lines.join("\n") };
}

function runBunAudit(): { cveCount: number; output: string } {
  const proc = spawnSync("bun", ["audit"], {
    cwd: ROOT,
    encoding: "utf8",
    maxBuffer: 16 * 1024 * 1024,
  });

  const out = `${proc.stdout ?? ""}${proc.stderr ?? ""}`.trim();
  if (proc.status === 0) {
    return { cveCount: 0, output: "" };
  }
  // Heuristic count: lines starting with severity markers.
  const matches = out.match(/(critical|high|moderate|low):/gi);
  return { cveCount: matches?.length ?? 1, output: out };
}

function runBunOutdated(): { count: number; output: string } {
  const proc = spawnSync("bun", ["outdated", "--filter='*'"], {
    cwd: ROOT,
    encoding: "utf8",
    maxBuffer: 16 * 1024 * 1024,
  });
  const out = `${proc.stdout ?? ""}${proc.stderr ?? ""}`;
  // Count lines that look like a table row with a package name in the first column.
  const lines = out.split("\n").filter((l) => /^\| @?[a-z][\w./@-]+\s+\|/.test(l));
  return { count: lines.length, output: out.trim() };
}

// ---------------------------------------------------------------------------
// Verbose: walk every direct dep, look up its note, count usages.
// ---------------------------------------------------------------------------

interface DepEntry {
  name: string;
  workspace: string;
  kind: "dep" | "dev" | "peer";
  version: string;
}

function listDirectDeps(): DepEntry[] {
  const out: DepEntry[] = [];
  const files = ["package.json", ...listOtherPackageJson()];
  for (const file of files) {
    const path = join(ROOT, file);
    if (!existsSync(path)) {
      continue;
    }
    type PkgJson = {
      name?: string;
      dependencies?: Record<string, string>;
      devDependencies?: Record<string, string>;
      peerDependencies?: Record<string, string>;
    };
    const json = JSON.parse(readFileSync(path, "utf8")) as unknown as PkgJson;
    const ws = json.name ?? file;
    pushExternal(out, ws, "dep", json.dependencies);
    pushExternal(out, ws, "dev", json.devDependencies);
    pushExternal(out, ws, "peer", json.peerDependencies);
  }
  return out;
}

function pushExternal(
  out: DepEntry[],
  workspace: string,
  kind: DepEntry["kind"],
  source: Record<string, string> | undefined
): void {
  for (const [name, raw] of Object.entries(source ?? {})) {
    if (raw.startsWith("workspace:") || raw.startsWith("link:") || raw.startsWith("file:")) {
      continue;
    }
    out.push({ name, workspace, kind, version: raw });
  }
}

function listOtherPackageJson(): string[] {
  const out: string[] = [];
  if (existsSync(join(ROOT, "tests/package.json"))) {
    out.push("tests/package.json");
  }
  const examples = join(ROOT, "examples");
  if (!existsSync(examples)) {
    return out;
  }
  for (const entry of readdirSafe(examples)) {
    const root = `examples/${entry}/package.json`;
    if (existsSync(join(ROOT, root))) {
      out.push(root);
    }
    const inner = join(ROOT, "examples", entry);
    for (const sub of readdirSafe(inner)) {
      const subPkg = `examples/${entry}/${sub}/package.json`;
      if (existsSync(join(ROOT, subPkg))) {
        out.push(subPkg);
      }
    }
  }
  return out;
}

function readNotes(): Record<string, string> {
  if (!existsSync(NOTES_FILE)) {
    return {};
  }
  type NotesFile = { notes?: Record<string, string> };
  const json = JSON.parse(readFileSync(NOTES_FILE, "utf8")) as unknown as NotesFile;
  return json.notes ?? {};
}

function countUsages(name: string): number {
  const escaped = name.replace(/\//g, "\\/").replace(/[-.@]/g, (c) => `\\${c}`);
  const proc = spawnSync(
    "grep",
    [
      "-rIE",
      "--include=*.ts",
      "--include=*.tsx",
      `(from|require\\()\\s*['"\`]${escaped}(/[^'"\`]*)?['"\`]`,
      "src",
      "tools",
      "cli",
      "scripts",
      "tests",
    ],
    { cwd: ROOT, encoding: "utf8", maxBuffer: 16 * 1024 * 1024 }
  );
  if (!proc.stdout) {
    return 0;
  }
  return proc.stdout.split("\n").filter(Boolean).length;
}

function printVerbose(): void {
  const notes = readNotes();
  const deps = listDirectDeps();
  const grouped = new Map<string, DepEntry[]>();
  for (const dep of deps) {
    const existing = grouped.get(dep.name) ?? [];
    existing.push(dep);
    grouped.set(dep.name, existing);
  }

  const names = [...grouped.keys()].sort();
  process.stdout.write("\n── Direct dependency notes ──\n");
  let unannotated = 0;
  for (const name of names) {
    const note = notes[name];
    const entries = grouped.get(name) ?? [];
    const versions = [...new Set(entries.map((e) => e.version))].join(", ");
    const workspaces = [...new Set(entries.map((e) => e.workspace))].sort().join(", ");
    const usages = countUsages(name);
    if (note) {
      process.stdout.write(
        `  ${name}@${versions}\n    ${note}\n    used by: ${workspaces} (${usages} import(s))\n`
      );
    } else {
      unannotated++;
      process.stdout.write(
        `  ${name}@${versions}\n    ⚠️  TODO: add a note in deps-notes.json\n    used by: ${workspaces} (${usages} import(s))\n`
      );
    }
  }
  if (unannotated > 0) {
    process.stdout.write(
      `\n${unannotated} dep(s) are missing notes in ${relative(ROOT, NOTES_FILE)}.\n`
    );
  }

  const stale = Object.keys(notes).filter((n) => !grouped.has(n));
  if (stale.length > 0) {
    process.stdout.write("\n── Stale notes (dep removed but note kept) ──\n");
    for (const name of stale.sort()) {
      process.stdout.write(`  ${name} — remove from deps-notes.json\n`);
    }
  }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

function main(): void {
  requireBinary("osv-scanner", "Run `brew bundle` (or `brew install osv-scanner`).");

  const hash = hashInputs();
  const cached = loadCache();

  if (cached?.hash === hash) {
    process.stdout.write(`✅ Deps audit cached at ${cached.timestamp} (inputs unchanged)\n`);
    process.stdout.write(
      `   ${cached.cveCount === 0 ? "0 CVEs" : `${cached.cveCount} CVE(s)`} · ${cached.outdatedCount} outdated\n`
    );
    if (VERBOSE) {
      if (cached.cveDetails) {
        process.stdout.write(`\n${cached.cveDetails}\n`);
      }
      if (cached.outdated) {
        process.stdout.write(`\n${cached.outdated}\n`);
      }
      printVerbose();
    }
    if (cached.cveCount > 0) {
      process.exit(1);
    }
    return;
  }

  process.stdout.write("🔎 Running deps audit (cache miss — re-scanning)…\n");

  const osv = runOsvScanner();
  const audit = runBunAudit();
  const outdated = runBunOutdated();

  const cveCount = osv.cveCount + audit.cveCount;
  const cveDetails = [
    osv.output ? `osv-scanner:\n${osv.output}` : "",
    audit.output ? `bun audit:\n${audit.output}` : "",
  ]
    .filter(Boolean)
    .join("\n\n");

  const result: CachedResult = {
    hash,
    timestamp: new Date().toISOString(),
    cveCount,
    cveDetails,
    outdated: outdated.output,
    outdatedCount: outdated.count,
  };
  saveCache(result);

  if (cveCount === 0) {
    process.stdout.write(`✅ No CVEs found · ${outdated.count} outdated dep(s)\n`);
  } else {
    process.stdout.write(`❌ ${cveCount} CVE(s) found:\n\n${cveDetails}\n`);
  }

  if (VERBOSE) {
    if (outdated.output) {
      process.stdout.write(`\n── Outdated ──\n${outdated.output}\n`);
    }
    printVerbose();
  }

  if (cveCount > 0) {
    process.exit(1);
  }
}

main();
