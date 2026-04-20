#!/usr/bin/env bun

/**
 * CLI entry point for Polly quality checks.
 *
 *   polly quality                    # run every check
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
 *   --exclude <a,b,c>                # comma-separated dir names
 *   --exclude-packages <a,b>         # no-as-casting only
 *   --exclude-files <a,b>            # no-as-casting only
 *   --pattern <glob>                 # no-as-casting / no-require
 */

import {
  checkCssLayout,
  checkCssQuality,
  checkCssUnused,
  checkCssVars,
  checkNoAsCasting,
  checkNoRequire,
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

let exitCode = 0;
switch (subcommand) {
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
      "Expected one of: no-as-casting, no-require, css, css-quality, css-layout, css-vars, css-unused"
    );
    exitCode = 2;
}

process.exit(exitCode);
