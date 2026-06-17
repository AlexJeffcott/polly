#!/usr/bin/env bun

/**
 * Polly check orchestrator.
 *
 * Dispatches to individual check scripts. Run a single check via
 * `bun run check <name>`, or run all of them via `bun run check all`.
 *
 * Implemented checks:
 *
 *   typecheck       bunx tsc --noEmit (root + tests workspace)
 *   lint            biome check . (formatting + lint rules)
 *   secrets         gitleaks scan with .gitleaks.toml allowlist
 *   gitignore       cross-checks .gitleaks.toml allowlist against .gitignore
 *   security        semgrep SAST with --config auto
 *   deps-audit      osv-scanner + bun audit + bun outdated (cached)
 *   deps            bans superseded dev tooling and deprecated runtime libs
 *   casts           bans `x as Y` outside `as const` and `as unknown as Y`
 *   boundaries      enforces src/ vs tools/ vs cli/ vs scripts/ direction
 *   server-imports  bans node:/bun: imports from browser-targeted code
 *   all             runs every check above concurrently; reports all failures
 *
 * `check all` drains the checks through a bounded worker pool (default
 * cpus-1, capped) and reports every failure rather than stopping at the
 * first. `--fail-fast` stops launching new checks after the first failure
 * (soft: in-flight checks still finish); `--concurrency N` overrides the pool
 * size; `--verbose` forces serial with live output. It always runs read-only
 * — individual checks may have their own --fix or --verbose flags but the
 * aggregate gate must never mutate source.
 */

import { existsSync, readFileSync } from "node:fs";
import { cpus } from "node:os";
import { dirname, join } from "node:path";
import { type BatchStep, runBatch } from "../tools/quality/src/check-runner";

const ROOT = process.cwd();

/** Nearest ancestor of cwd (inclusive) holding `.gitleaks.toml`. The config
 * lives at the monorepo root, one level above this package since the
 * packages/ restructure, and the secret scan should cover the whole repo
 * (its allowlist names root-level dirs like examples/ and recipes/). */
function secretsRoot(): string {
  let dir = ROOT;
  while (!existsSync(join(dir, ".gitleaks.toml"))) {
    const parent = dirname(dir);
    if (parent === dir) return ROOT;
    dir = parent;
  }
  return dir;
}

async function spawn(args: string[], cwd: string = ROOT): Promise<number> {
  const proc = Bun.spawn(args, { cwd, stdout: "inherit", stderr: "inherit" });
  await proc.exited;
  return proc.exitCode ?? 1;
}

async function spawnQuiet(args: string[]): Promise<number> {
  const proc = Bun.spawn(args, { cwd: ROOT, stdout: "ignore", stderr: "ignore" });
  await proc.exited;
  return proc.exitCode ?? 1;
}

async function requireBinary(name: string, hint: string): Promise<boolean> {
  const code = await spawnQuiet(["which", name]);
  if (code !== 0) {
    process.stderr.write(`❌ ${name} is required but not on PATH.\n   ${hint}\n`);
    return false;
  }
  return true;
}

// ───────────────────────────────────────────────────────────────────────────

async function checkTypecheck(): Promise<boolean> {
  const code = await spawn(["bun", "run", "typecheck"]);
  if (code === 0) {
    process.stdout.write("✅ Typecheck clean (tsc --noEmit)\n");
  }
  return code === 0;
}

async function checkLint(): Promise<boolean> {
  const code = await spawn(["bun", "run", "lint"]);
  if (code === 0) {
    process.stdout.write("✅ Lint clean (biome check)\n");
  }
  return code === 0;
}

async function checkSecrets(): Promise<boolean> {
  if (!(await requireBinary("gitleaks", "Run `brew bundle` (or `brew install gitleaks`)."))) {
    return false;
  }
  const code = await spawn(
    ["gitleaks", "detect", "--source", ".", "--no-git", "-c", ".gitleaks.toml"],
    secretsRoot()
  );
  if (code === 0) {
    process.stdout.write("✅ No secrets found (gitleaks)\n");
  }
  return code === 0;
}

async function checkSecurity(verbose: boolean): Promise<boolean> {
  if (!(await requireBinary("semgrep", "Run `brew bundle` (or `brew install semgrep`)."))) {
    return false;
  }
  const args = [
    "semgrep",
    "scan",
    "--config",
    "auto",
    "--severity",
    "ERROR",
    "--severity",
    "WARNING",
    "--exclude=Dockerfile*",
    "--exclude=docker-compose*",
    "--error",
  ];
  if (!verbose) {
    args.push("--quiet");
  }
  const code = await spawn(args);
  if (code === 0) {
    process.stdout.write("✅ No security issues found (semgrep)\n");
  }
  return code === 0;
}

async function checkDepsAudit(verbose: boolean): Promise<boolean> {
  const args = ["bun", "scripts/check-deps-audit.ts"];
  if (verbose) {
    args.push("--verbose");
  }
  return (await spawn(args)) === 0;
}

async function checkForbiddenDeps(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-no-forbidden-deps.ts"])) === 0;
}

async function checkCasts(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-no-as-casting.ts"])) === 0;
}

async function checkBoundaries(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-package-boundaries.ts"])) === 0;
}

async function checkServerImports(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-no-server-imports.ts"])) === 0;
}

async function checkNoTodoTests(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-no-todo-tests.ts"])) === 0;
}

async function checkSuppressions(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-suppression-justifications.ts"])) === 0;
}

async function checkMutateTargets(): Promise<boolean> {
  return (await spawn(["bun", "scripts/check-mutate-targets.ts"])) === 0;
}

interface MustIgnoreEntry {
  pattern: string;
  filename: string;
}

const SECTION_OPEN_MARKERS = ["Gitignored files", "Local dev TLS certs"];
const SECTION_CLOSE_MARKERS = ["Test fixtures", "Sanitised production"];

function isSectionMarker(line: string, markers: string[]): boolean {
  return markers.some((m) => line.includes(m));
}

function parseMustIgnore(toml: string): MustIgnoreEntry[] {
  const out: MustIgnoreEntry[] = [];
  let inSection = false;
  for (const line of toml.split("\n")) {
    if (isSectionMarker(line, SECTION_OPEN_MARKERS)) {
      inSection = true;
      continue;
    }
    if (isSectionMarker(line, SECTION_CLOSE_MARKERS)) {
      inSection = false;
      continue;
    }
    if (!inSection) {
      continue;
    }
    const match = line.match(/'''(.+?)'''/);
    if (!match?.[1]) {
      continue;
    }
    const regex = match[1];
    out.push({ pattern: regex, filename: regex.replace(/\\\./g, ".").replace(/\$$/, "") });
  }
  return out;
}

function gitignoreCoversFilename(gi: string, filename: string): boolean {
  if (!gi || gi.startsWith("#")) {
    return false;
  }
  if (gi === filename) {
    return true;
  }
  // .env covers .env.local etc.
  if (filename.startsWith(`${gi}.`) || filename.startsWith(`${gi}/`)) {
    return true;
  }
  const dirMatch = gi.match(/^\*?\*?\/?(.+)\/$/);
  if (dirMatch?.[1] && filename.startsWith(dirMatch[1])) {
    return true;
  }
  return gi.endsWith("/") && filename.startsWith(gi);
}

async function checkGitignore(): Promise<boolean> {
  const root = secretsRoot();
  const tomlPath = join(root, ".gitleaks.toml");
  const gitignorePath = join(root, ".gitignore");
  if (!existsSync(tomlPath)) {
    process.stdout.write("⏩ No .gitleaks.toml — skipping gitignore check\n");
    return true;
  }

  const toml = readFileSync(tomlPath, "utf8");
  const gitignore = existsSync(gitignorePath) ? readFileSync(gitignorePath, "utf8") : "";

  const mustIgnore = parseMustIgnore(toml);
  const gitignoreLines = gitignore.split("\n").map((l) => l.trim());
  const missing = mustIgnore
    .filter(({ filename }) => !gitignoreLines.some((gi) => gitignoreCoversFilename(gi, filename)))
    .map((e) => e.filename);

  if (missing.length === 0) {
    process.stdout.write("✅ All gitleaks-allowlisted secret paths are gitignored\n");
    return true;
  }
  process.stderr.write("❌ Files allowed by .gitleaks.toml are NOT in .gitignore:\n");
  for (const f of missing) {
    process.stderr.write(`   ${f}\n`);
  }
  process.stderr.write("   Add them to .gitignore so allowlisting can't accept a real secret.\n");
  return false;
}

// ───────────────────────────────────────────────────────────────────────────

const KNOWN_CHECKS = [
  "typecheck",
  "lint",
  "secrets",
  "gitignore",
  "security",
  "deps-audit",
  "deps",
  "casts",
  "boundaries",
  "server-imports",
  "todo-tests",
  "suppressions",
  "mutate-targets",
  "all",
] as const;

type CheckName = (typeof KNOWN_CHECKS)[number];

function showHelp(): void {
  process.stdout.write(`
Usage: bun run check <subcommand>

Subcommands:
  typecheck       tsc --noEmit (root + tests workspace)
  lint            biome check (formatting + lint rules)
  secrets         gitleaks secret scanning
  gitignore       gitleaks allowlist must be reflected in .gitignore
  security        semgrep SAST scan
  deps-audit      osv-scanner + bun audit (cached)
  deps            forbidden dev/runtime dependencies
  casts           no-as-casting type-assertion ban
  boundaries      src/ vs tools/ vs cli/ vs scripts/ direction
  server-imports  no node:/bun: imports in browser-targeted code
  todo-tests      no it.todo / test.failing forms under tests/
  suppressions    new biome-ignore/ts-ignore must carry a ticket reference
  mutate-targets  every stryker.conf.json mutate path still exists
  all             every check above, concurrently (reports all failures)

Options:
  --verbose       stream output live; for 'all', forces a serial pool (N=1)
  --concurrency N for 'all', run the checks in a bounded pool of N
                  (default: cpus-1, capped at ${DEFAULT_MAX_CONCURRENCY})
  --fail-fast     for 'all', stop launching new checks after the first failure
                  (soft: in-flight checks still finish). Default: run all
`);
}

async function runOne(name: CheckName, verbose: boolean): Promise<boolean> {
  switch (name) {
    case "typecheck":
      return checkTypecheck();
    case "lint":
      return checkLint();
    case "secrets":
      return checkSecrets();
    case "gitignore":
      return checkGitignore();
    case "security":
      return checkSecurity(verbose);
    case "deps-audit":
      return checkDepsAudit(verbose);
    case "deps":
      return checkForbiddenDeps();
    case "casts":
      return checkCasts();
    case "boundaries":
      return checkBoundaries();
    case "server-imports":
      return checkServerImports();
    case "todo-tests":
      return checkNoTodoTests();
    case "suppressions":
      return checkSuppressions();
    case "mutate-targets":
      return checkMutateTargets();
    case "all":
      return runAll(verbose);
  }
}

/**
 * The full gate, in registry order: each entry maps a display name to the
 * `check <sub>` it runs. `runAll` spawns each as its own subprocess so the pool
 * can capture per-check output and report every failure — the individual check
 * functions print straight to stdout, which only stays legible one at a time.
 */
const ALL_CHECK_STEPS: Array<{ sub: CheckName; name: string }> = [
  { sub: "typecheck", name: "Typecheck" },
  { sub: "lint", name: "Lint" },
  { sub: "gitignore", name: "Gitignore" },
  { sub: "secrets", name: "Secrets" },
  { sub: "security", name: "Security" },
  { sub: "deps-audit", name: "Dependency Audit" },
  { sub: "deps", name: "Forbidden Deps" },
  { sub: "casts", name: "Casts" },
  { sub: "boundaries", name: "Module Boundaries" },
  { sub: "server-imports", name: "Server Imports" },
  { sub: "todo-tests", name: "No .todo/.failing tests" },
  { sub: "suppressions", name: "Suppression Justifications" },
  { sub: "mutate-targets", name: "Mutate Targets" },
];

/**
 * Multi-second external scans. The pool drains steps in array order, so in
 * run-all mode (no early abort) hoisting these into the first slots lets every
 * cheaper check pack in behind them and collapses wall-clock toward the slowest
 * one. Under --fail-fast we leave them where they are: a worker can't un-spawn a
 * 12s scan, so front-loading one would defeat the early abort.
 */
const LONG_POLE_CHECKS = new Set<CheckName>(["security", "deps-audit", "secrets"]);

/** Hoist the long poles to the front, preserving relative order otherwise. */
function hoistLongPoles<T extends { sub: CheckName }>(steps: T[]): T[] {
  const poles = steps.filter((s) => LONG_POLE_CHECKS.has(s.sub));
  if (poles.length === 0) return steps;
  return [...poles, ...steps.filter((s) => !LONG_POLE_CHECKS.has(s.sub))];
}

/** Cap the auto pool: `tsc`/`semgrep` are memory-hungry, so don't oversubscribe. */
const DEFAULT_MAX_CONCURRENCY = 8;

/** Read `--concurrency N` (space form) or `--concurrency=N` from argv. */
function readConcurrencyFlag(argv: string[]): string | undefined {
  const eq = argv.find((a) => a.startsWith("--concurrency="));
  if (eq) return eq.slice("--concurrency=".length);
  const idx = argv.indexOf("--concurrency");
  return idx === -1 ? undefined : argv[idx + 1];
}

/** Resolve the pool size. `--verbose` streams live, which only reads right one
 * step at a time, so it forces serial. */
function resolveConcurrency(verbose: boolean, argv: string[]): number {
  if (verbose) return 1;
  const raw = readConcurrencyFlag(argv);
  if (raw !== undefined) {
    const n = Number(raw);
    if (Number.isFinite(n) && n >= 1) return Math.floor(n);
  }
  return Math.max(1, Math.min(cpus().length - 1, DEFAULT_MAX_CONCURRENCY));
}

async function runAll(verbose: boolean): Promise<boolean> {
  const argv = process.argv.slice(2);
  const concurrency = resolveConcurrency(verbose, argv);
  const failFast = argv.includes("--fail-fast");

  // Spawn this same file with one subcommand per check (see ALL_CHECK_STEPS).
  const self = import.meta.path;
  const verboseArgs = verbose ? ["--verbose"] : [];
  const ordered = failFast ? ALL_CHECK_STEPS : hoistLongPoles(ALL_CHECK_STEPS);
  const steps: BatchStep[] = ordered.map((c) => ({
    name: c.name,
    cmd: ["bun", self, c.sub, ...verboseArgs],
    cwd: ROOT,
  }));

  process.stdout.write("── check all ──\n");
  if (concurrency > 1) {
    process.stdout.write(
      `   ${steps.length} checks · pool of ${concurrency} · ${failFast ? "fail-fast" : "run-all"} (use --verbose for serial + live output)\n`
    );
  }

  const result = await runBatch({ steps, verbose, failFast, concurrency });
  const elapsed = (result.totalDurationMs / 1000).toFixed(1);

  if (result.ok) {
    process.stdout.write(`\n✅ All checks passed! (${elapsed}s)\n`);
    return true;
  }
  process.stderr.write(
    `\n❌ ${result.failed.length} check(s) failed: ${result.failed.join(", ")} (${elapsed}s)\n`
  );
  return false;
}

const args = process.argv.slice(2);
const verbose = args.includes("--verbose") || args.includes("-v");
const positional = args.filter((a) => !a.startsWith("-"));
const subcommand = positional[0];

if (!subcommand || subcommand === "help" || subcommand === "--help") {
  showHelp();
  process.exit(0);
}

if (!KNOWN_CHECKS.includes(subcommand as unknown as CheckName)) {
  process.stderr.write(`❌ Unknown subcommand: ${subcommand}\n`);
  showHelp();
  process.exit(1);
}

const ok = await runOne(subcommand as unknown as CheckName, verbose);
process.exit(ok ? 0 : 1);
