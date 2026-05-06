#!/usr/bin/env bun

/**
 * CLI entry point for Polly quality checks.
 *
 * Plugin-host subcommands (preferred):
 *   polly quality list                       # list registered checks
 *   polly quality run                        # run every registered check
 *   polly quality run polly:no-as-casting    # run a specific id (or several)
 *   polly quality run all                    # alias for `run`
 *
 * Legacy subcommands (back-compat with the pre-host CLI):
 *   polly quality no-as-casting      # only the TS casting check
 *   polly quality no-require         # ban require(...) calls
 *   polly quality css                # all CSS checks
 *   polly quality css-quality        # only hardcoded-values check
 *   polly quality css-layout         # only Layout-usage check
 *   polly quality css-vars           # only undefined-variable check
 *   polly quality css-unused         # only unused-selector check (advisory)
 *
 * Shared flags:
 *   --root <dir>                     # defaults to process.cwd()
 *   --config <path>                  # explicit polly.config.ts path
 *   --no-cache                       # bypass the on-disk cache
 *   --exclude <a,b,c>                # legacy: comma-separated dir names
 *   --exclude-packages <a,b>         # legacy: no-as-casting only
 *   --exclude-files <a,b>            # legacy: no-as-casting only
 *   --pattern <glob>                 # legacy: no-as-casting / no-require
 */

import {
  checkCssLayout,
  checkCssQuality,
  checkCssUnused,
  checkCssVars,
  checkNoAsCasting,
  checkNoRequire,
  listChecks,
  loadQualityConfig,
  registerPlugins,
  runChecks,
  validateRunConfig,
} from "./index";
import { logger } from "./logger";

const args = process.argv.slice(2);

function getFlag(name: string): string | undefined {
  const idx = args.indexOf(`--${name}`);
  return idx >= 0 ? args[idx + 1] : undefined;
}

function getSubcommand(): string {
  for (const arg of args) {
    if (!arg.startsWith("--")) return arg;
  }
  return "all";
}

const subcommand = getSubcommand();
const rootDir = getFlag("root") ?? process.cwd();
const exclude = getFlag("exclude")?.split(",") ?? [
  "node_modules",
  "dist",
  ".git",
  ".bun",
  "dist-test",
  "build",
  "coverage",
];
const excludePackages = getFlag("exclude-packages")?.split(",");
const excludeFiles = getFlag("exclude-files")?.split(",");
const filePatterns = getFlag("pattern");

async function runNoAsCasting(): Promise<number> {
  const result = await checkNoAsCasting({
    rootDir,
    exclude,
    ...(excludePackages ? { excludePackages } : {}),
    ...(excludeFiles ? { excludeFiles } : {}),
    ...(filePatterns ? { filePatterns } : {}),
  });
  result.print();
  return result.violations.length > 0 ? 1 : 0;
}

async function runNoRequire(): Promise<number> {
  const result = await checkNoRequire({
    rootDir,
    exclude,
    ...(filePatterns ? { filePatterns } : {}),
  });
  result.print();
  return result.violations.length > 0 ? 1 : 0;
}

async function runCssQuality(): Promise<number> {
  const r = await checkCssQuality({ rootDir, skipDirs: exclude });
  r.print();
  return r.violations.length > 0 ? 1 : 0;
}

async function runCssLayout(): Promise<number> {
  const r = await checkCssLayout({ rootDir, skipDirs: exclude });
  r.print();
  return r.violations.length > 0 ? 1 : 0;
}

async function runCssVars(): Promise<number> {
  const r = await checkCssVars({ rootDir, skipDirs: exclude });
  r.print();
  return r.violations.length > 0 ? 1 : 0;
}

async function runCssUnused(): Promise<number> {
  const r = await checkCssUnused({ rootDir, skipDirs: exclude });
  r.print();
  return 0;
}

async function runCssAll(): Promise<number> {
  const results = [
    await runCssQuality(),
    await runCssLayout(),
    await runCssVars(),
    await runCssUnused(),
  ];
  return results.some((code) => code !== 0) ? 1 : 0;
}

async function runAll(): Promise<number> {
  const results = [await runNoAsCasting(), await runNoRequire(), await runCssAll()];
  return results.some((code) => code !== 0) ? 1 : 0;
}

async function runHostList(): Promise<number> {
  const config = await loadQualityConfig(rootDir, getFlag("config"));
  const registry = registerPlugins(config.plugins);
  for (const c of listChecks(registry)) {
    logger.log(`  ${c.id.padEnd(40)} ${c.description}`);
  }
  return 0;
}

const VALUE_FLAGS = new Set([
  "root",
  "config",
  "exclude",
  "exclude-packages",
  "exclude-files",
  "pattern",
]);

function collectRunPositionals(): string[] {
  // Positional args after the `run` subcommand are the requested ids.
  const runIdx = args.indexOf("run");
  const out: string[] = [];
  for (let i = runIdx + 1; i < args.length; i++) {
    const a = args[i];
    if (!a) continue;
    if (a.startsWith("--")) {
      if (VALUE_FLAGS.has(a.slice(2))) i++;
      continue;
    }
    out.push(a);
  }
  return out;
}

function reportRunResult(r: {
  id: string;
  ok: boolean;
  cached: boolean;
  durationMs: number;
  messages: string[];
  error?: string;
}): void {
  const tag = r.cached ? "cached " : "       ";
  if (r.ok) {
    logger.log(`  ✓ ${tag}${r.id} (${r.durationMs}ms)`);
    return;
  }
  logger.log(`  ✗ ${tag}${r.id} (${r.durationMs}ms)`);
  if (r.error) logger.error(`      error: ${r.error}`);
  for (const m of r.messages) logger.log(`      ${m}`);
}

async function runHostRun(): Promise<number> {
  const config = await loadQualityConfig(rootDir, getFlag("config"));
  const registry = registerPlugins(config.plugins);
  const validationErrors = validateRunConfig(registry, config);
  if (validationErrors.length > 0) {
    for (const err of validationErrors) logger.error(err);
    return 2;
  }
  const positional = collectRunPositionals();
  const ids =
    positional.length === 0 || (positional.length === 1 && positional[0] === "all")
      ? undefined
      : positional;
  const report = await runChecks(registry, config, ids, {
    rootDir,
    noCache: args.includes("--no-cache"),
  });
  for (const r of report.results) reportRunResult(r);
  return report.ok ? 0 : 1;
}

let exitCode = 0;
switch (subcommand) {
  case "list":
    exitCode = await runHostList();
    break;
  case "run":
    exitCode = await runHostRun();
    break;
  case "no-as-casting":
    exitCode = await runNoAsCasting();
    break;
  case "no-require":
    exitCode = await runNoRequire();
    break;
  case "css":
    exitCode = await runCssAll();
    break;
  case "css-quality":
    exitCode = await runCssQuality();
    break;
  case "css-layout":
    exitCode = await runCssLayout();
    break;
  case "css-vars":
    exitCode = await runCssVars();
    break;
  case "css-unused":
    exitCode = await runCssUnused();
    break;
  case "all":
    exitCode = await runAll();
    break;
  default:
    logger.error(`Unknown quality subcommand: ${subcommand}`);
    logger.error(
      "Expected one of: list, run, no-as-casting, no-require, css, css-quality, css-layout, css-vars, css-unused"
    );
    exitCode = 2;
}

process.exit(exitCode);
