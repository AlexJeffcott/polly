#!/usr/bin/env bun

/**
 * Polly check orchestrator.
 *
 * Dispatches to individual check scripts. Run a single check via
 * `bun run check <name>`, or run all of them via `bun run check all`.
 *
 * Implemented checks:
 *
 *   secrets         gitleaks scan with .gitleaks.toml allowlist
 *   gitignore       cross-checks .gitleaks.toml allowlist against .gitignore
 *   security        semgrep SAST with --config auto
 *   deps-audit      osv-scanner + bun audit + bun outdated (cached)
 *   deps            bans superseded dev tooling and deprecated runtime libs
 *   casts           bans `x as Y` outside `as const` and `as unknown as Y`
 *   boundaries      enforces src/ vs tools/ vs cli/ vs scripts/ direction
 *   server-imports  bans node:/bun: imports from browser-targeted code
 *   all             runs every check above; aborts on first failure
 *
 * `check all` always runs read-only — individual checks may have their
 * own --fix or --verbose flags but the aggregate gate must never mutate
 * source.
 */

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

const ROOT = process.cwd();

interface CheckResult {
  name: string;
  ok: boolean;
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

async function checkSecrets(): Promise<boolean> {
  if (!(await requireBinary("gitleaks", "Run `brew bundle` (or `brew install gitleaks`)."))) {
    return false;
  }
  const code = await spawn([
    "gitleaks",
    "detect",
    "--source",
    ".",
    "--no-git",
    "-c",
    ".gitleaks.toml",
  ]);
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

async function checkGitignore(): Promise<boolean> {
  const tomlPath = join(ROOT, ".gitleaks.toml");
  const gitignorePath = join(ROOT, ".gitignore");
  if (!existsSync(tomlPath)) {
    process.stdout.write("⏩ No .gitleaks.toml — skipping gitignore check\n");
    return true;
  }

  const toml = readFileSync(tomlPath, "utf8");
  const gitignore = existsSync(gitignorePath) ? readFileSync(gitignorePath, "utf8") : "";

  // Pull paths between "Gitignored files" and "Test fixtures" comments —
  // those are the ones that MUST also be in .gitignore.
  const lines = toml.split("\n");
  const mustIgnore: { pattern: string; filename: string }[] = [];
  let inGitignoreSection = false;

  for (const line of lines) {
    if (line.includes("Gitignored files") || line.includes("Local dev TLS certs")) {
      inGitignoreSection = true;
      continue;
    }
    if (line.includes("Test fixtures") || line.includes("Sanitised production")) {
      inGitignoreSection = false;
      continue;
    }
    if (!inGitignoreSection) {
      continue;
    }
    const match = line.match(/'''(.+?)'''/);
    if (!match?.[1]) {
      continue;
    }
    const regex = match[1];
    const filename = regex.replace(/\\\./g, ".").replace(/\$$/, "");
    mustIgnore.push({ pattern: regex, filename });
  }

  const gitignoreLines = gitignore.split("\n").map((l) => l.trim());
  const missing: string[] = [];

  for (const { filename } of mustIgnore) {
    const covered = gitignoreLines.some((gi) => {
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
      if (gi.endsWith("/") && filename.startsWith(gi)) {
        return true;
      }
      return false;
    });
    if (!covered) {
      missing.push(filename);
    }
  }

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
  "secrets",
  "gitignore",
  "security",
  "deps-audit",
  "deps",
  "casts",
  "boundaries",
  "server-imports",
  "all",
] as const;

type CheckName = (typeof KNOWN_CHECKS)[number];

function showHelp(): void {
  process.stdout.write(`
Usage: bun run check <subcommand>

Subcommands:
  secrets         gitleaks secret scanning
  gitignore       gitleaks allowlist must be reflected in .gitignore
  security        semgrep SAST scan
  deps-audit      osv-scanner + bun audit (cached)
  deps            forbidden dev/runtime dependencies
  casts           no-as-casting type-assertion ban
  boundaries      src/ vs tools/ vs cli/ vs scripts/ direction
  server-imports  no node:/bun: imports in browser-targeted code
  all             every check above

Options:
  --verbose       passes through to checks that support it (security, deps-audit)
`);
}

async function runOne(name: CheckName, verbose: boolean): Promise<boolean> {
  switch (name) {
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
    case "all":
      return runAll(verbose);
  }
}

async function runAll(verbose: boolean): Promise<boolean> {
  const checks: Array<{ name: string; fn: () => Promise<boolean> }> = [
    { name: "Gitignore", fn: () => checkGitignore() },
    { name: "Secrets", fn: () => checkSecrets() },
    { name: "Security", fn: () => checkSecurity(verbose) },
    { name: "Dependency Audit", fn: () => checkDepsAudit(verbose) },
    { name: "Forbidden Deps", fn: () => checkForbiddenDeps() },
    { name: "Casts", fn: () => checkCasts() },
    { name: "Module Boundaries", fn: () => checkBoundaries() },
    { name: "Server Imports", fn: () => checkServerImports() },
  ];

  const results: CheckResult[] = [];
  for (const check of checks) {
    process.stdout.write(`\n── ${check.name} ──\n`);
    const ok = await check.fn();
    results.push({ name: check.name, ok });
    if (!ok) {
      process.stderr.write(`\n❌ ${check.name} failed — aborting check:all\n`);
      return false;
    }
  }
  process.stdout.write("\n✅ All checks passed!\n");
  return true;
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
