#!/usr/bin/env bun
/**
 * Polly CLI
 *
 * Command-line tool for building multi-execution-context applications
 * with reactive state and cross-context messaging.
 *
 * Supports: Chrome extensions, PWAs, Node/Bun/Deno apps with workers
 *
 * Usage:
 *   polly init [name] [--type=TYPE]  Create a new project
 *   polly check                      Run all checks (typecheck, lint, test, build)
 *   polly build [options]            Build the project
 *   polly dev                        Build with watch mode
 *   polly typecheck                  Type check your code
 *   polly lint [--fix]               Lint your code
 *   polly format                     Format your code
 *   polly test [args]                Run tests (requires bun test)
 *   polly test:browser [dir]         Run *.browser.{ts,tsx} in Puppeteer
 *   polly coverage [flags]           Coverage policy + orphan + mutate-target checks
 *   polly mutate [args]              Mutation testing + useless-test detection
 *   polly verify [args]              Run formal verification
 *   polly visualize [args]           Generate architecture diagrams
 *   polly quality [args]             Run quality conformance checks
 *   polly help                       Show help
 *
 * Project Types (init --type):
 *   extension           Chrome/Firefox extension (default)
 *   pwa                 Progressive Web App with workers
 *   websocket           WebSocket server application
 *   generic             Generic TypeScript project
 *
 * Options:
 *   --prod              Build for production (minified)
 *   --config <path>     Path to config file (default: polly.config.ts)
 *   --fix               Auto-fix lint/format issues
 *   --type=TYPE         Project type for init command
 */

import { constants as osConstants } from "node:os";
import {
  COMMAND_TOOL_PACKAGES,
  missingToolPackages,
  missingToolPackagesMessage,
} from "../tools/tool-deps/src/index.ts";

// Use Bun built-ins instead of Node.js APIs
const __dirname = import.meta.dir;

const command = process.argv[2];
const commandArgs = process.argv.slice(3);
const cwd = process.cwd();

// Parse arguments
const args = {
  prod: process.argv.includes("--prod"),
  config: process.argv.includes("--config")
    ? process.argv[process.argv.indexOf("--config") + 1]
    : undefined,
};

/** Signals the wrapper relays to its child instead of dying on them. */
const FORWARDED_SIGNALS = ["SIGINT", "SIGTERM", "SIGHUP"] as const;

/** Spawn options every subcommand passes; output always goes to the terminal. */
interface ChildOptions {
  cwd: string;
  stdout: "inherit";
  stderr: "inherit";
  stdin?: "inherit";
  env?: Record<string, string | undefined>;
}

/**
 * A subcommand's child exited non-zero. `exitCode` is the status the wrapper
 * should exit with: the child's own code, or 128 + signal number when the
 * child was killed by a signal (the shell convention).
 */
class ChildExitError extends Error {
  readonly exitCode: number;
  constructor(message: string, exitCode: number) {
    super(message);
    this.name = "ChildExitError";
    this.exitCode = exitCode;
  }
}

/**
 * Stop before spawning a tool whose optional peer packages are not installed.
 * The tools import them at load time, so without this check the child dies
 * on a bare "Cannot find package" resolve error. Resolution starts from this
 * file's directory: the bundled tools sit beside it under the same
 * node_modules chain.
 */
function requireToolPackages(name: string): void {
  const needed = COMMAND_TOOL_PACKAGES[name] ?? [];
  const missing = missingToolPackages(needed, __dirname);
  if (missing.length === 0) return;
  process.stderr.write(`❌ ${missingToolPackagesMessage(`polly ${name}`, missing)}\n`);
  process.exit(1);
}

/**
 * Run a subcommand's child process to completion and return its exit status.
 *
 * Without this, SIGTERM/SIGHUP to the wrapper killed only the wrapper and left
 * the child (e.g. `visualize serve`) running as an orphan, still holding its
 * port and the wrapper's stdout/stderr pipes. While the child runs, the
 * wrapper catches SIGINT/SIGTERM/SIGHUP and relays each one to it, then exits
 * with the child's status once the child has gone.
 *
 * Ctrl-C in a terminal delivers SIGINT to the child directly (same process
 * group) as well as through the relay. That second SIGINT is harmless: the
 * tools either take the default action or run an idempotent shutdown, and
 * kill() on an already-exited child is a no-op. The listeners are removed as
 * soon as the child exits, so they never hold the wrapper open.
 */
async function runChild(cmd: string[], options: ChildOptions): Promise<number> {
  const proc = Bun.spawn(cmd, options);
  const relay = (signal: NodeJS.Signals): void => {
    proc.kill(signal);
  };
  for (const signal of FORWARDED_SIGNALS) process.on(signal, relay);
  try {
    await proc.exited;
  } finally {
    for (const signal of FORWARDED_SIGNALS) process.off(signal, relay);
  }
  const signal = proc.signalCode;
  if (signal !== null) {
    return 128 + (typeof signal === "number" ? signal : osConstants.signals[signal]);
  }
  return proc.exitCode ?? 1;
}

/**
 * Load user's configuration
 */
async function loadConfig() {
  const configPaths = [
    args.config,
    `${cwd}/polly.config.ts`,
    `${cwd}/polly.config.js`,
    `${cwd}/polly.config.mjs`,
  ].filter((path): path is string => typeof path === "string" && path !== "");

  for (const configPath of configPaths) {
    // Use Bun.file().exists() instead of existsSync
    if (await Bun.file(configPath).exists()) {
      try {
        const config = await import(configPath);
        return config.default || config;
      } catch (error) {
        console.log(`❌ Failed to load config: ${configPath}`);
        throw error;
      }
    }
  }
  return {
    srcDir: "src",
    distDir: "dist",
    manifest: "manifest.json",
  };
}

/**
 * Build command - build the extension
 */
async function build() {
  const config = await loadConfig();

  // Check if bundled (published) or in monorepo
  const bundledScript = `${__dirname}/../scripts/build-extension.js`;
  const monorepoScript = `${__dirname}/../scripts/build-extension.ts`;
  const buildScriptPath = (await Bun.file(bundledScript).exists()) ? bundledScript : monorepoScript;

  // Pass config via environment
  process.env["WEB_EXT_SRC"] = `${cwd}/${config.srcDir || "src"}`;
  process.env["WEB_EXT_DIST"] = `${cwd}/${config.distDir || "dist"}`;
  process.env["WEB_EXT_MANIFEST"] = `${cwd}/${config.manifest || "manifest.json"}`;
  process.env["WEB_EXT_CWD"] = cwd;
  process.env["WEB_EXT_PROD"] = args.prod ? "true" : "false";

  // Run build
  const exitCode = await runChild(["bun", buildScriptPath], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });
  if (exitCode !== 0) {
    process.exit(exitCode);
  }
}

/**
 * Dev command - build with watch mode
 */
async function dev() {
  await build();
}

/**
 * Verify command - delegate to @fairfox/web-ext-verify
 */
async function verify() {
  requireToolPackages("verify");
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/verify/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/verify/src/cli.ts`;
  const verifyCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", verifyCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Verification failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Mutate command - delegate to tools/mutate (mutation engine + useless-test detection)
 */
async function mutate() {
  requireToolPackages("mutate");
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/mutate/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/mutate/src/cli.ts`;
  const mutateCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  // Pass the full commandArgs through — the tool's own cli reads the subcommand
  // (run/report/decisions/verify) as its first positional.
  const exitCode = await runChild(["bun", mutateCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Mutation testing failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * BDD command - delegate to tools/bdd (executable Gherkin against the model)
 */
async function bdd() {
  requireToolPackages("bdd");
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/bdd/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/bdd/src/cli.ts`;
  const bddCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  // Pass the full commandArgs through — the tool's own cli reads the subcommand
  // (run/check/new) as its first positional.
  const exitCode = await runChild(["bun", bddCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`BDD run failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Visualize command - delegate to @fairfox/polly-visualize
 */
async function visualize() {
  requireToolPackages("visualize");
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/visualize/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/visualize/src/cli.ts`;
  const visualizeCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", visualizeCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Visualization failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Gallery command - delegate to tools/gallery (serve/export the polly-ui gallery)
 */
async function gallery() {
  const bundledCli = `${__dirname}/../tools/gallery/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/gallery/src/cli.ts`;
  const galleryCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", galleryCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Gallery failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Quality command - delegate to @fairfox/polly-quality
 */
async function quality() {
  const bundledCli = `${__dirname}/../tools/quality/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/quality/src/cli.ts`;
  const qualityCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", qualityCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Quality checks failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Typecheck command - run TypeScript type checking
 */
async function typecheck() {
  const exitCode = await runChild(["bun", "--check"], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Type checking failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Lint command - run Biome linter
 */
async function lint() {
  const fix = commandArgs.includes("--fix");
  const lintArgs = fix ? ["check", "--write", "."] : ["check", "."];

  const exitCode = await runChild(["bunx", "@biomejs/biome", ...lintArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Linting failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Format command - run Biome formatter
 */
async function format() {
  const exitCode = await runChild(["bunx", "@biomejs/biome", "format", "--write", "."], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Formatting failed with exit code ${exitCode}`, exitCode);
  }
}

/** Flags that switch `polly test` into the tiered runner. */
const TIER_MODE_FLAGS = [
  "--tier",
  "--all",
  "--full",
  "--list",
  "--only",
  "--bail",
  "--strict-needs",
];

/** True when `polly test` should run the multi-tier orchestrator. */
function isTierMode(rawArgs: string[]): boolean {
  return rawArgs.some(
    (a) => TIER_MODE_FLAGS.includes(a) || a.startsWith("--tier") || a.startsWith("--only")
  );
}

/**
 * Tiered test command — `polly test --tier=… / --all / --full / --list`.
 * Drives the multi-tier engine with structured, timed reporting.
 *
 * Dispatch is by binary location, not cwd: inside the Polly repo (source
 * binary) it runs Polly's OWN suite via scripts/test/cli.ts; for an installed
 * package (scripts/ isn't shipped) it runs consumer auto-discovery, which
 * builds a plan from the consumer's own tests (tools/test/src/tiers/cli).
 */
async function testTiers() {
  const monorepoCli = `${__dirname}/../scripts/test/cli.ts`;
  const bundledConsumer = `${__dirname}/../tools/test/src/tiers/cli.js`;
  const sourceConsumer = `${__dirname}/../tools/test/src/tiers/cli.ts`;

  let runnerCli: string;
  if (await Bun.file(monorepoCli).exists()) {
    runnerCli = monorepoCli; // in the Polly repo: Polly's own tiered suite
  } else if (await Bun.file(bundledConsumer).exists()) {
    runnerCli = bundledConsumer; // installed package: discover the consumer's tiers
  } else {
    runnerCli = sourceConsumer;
  }

  const exitCode = await runChild(["bun", runnerCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Tiered tests failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Coverage command — per-file coverage policy, orphan detection, and
 * mutate-target validation. Zero-config in a consumer project; inside the
 * Polly repo it runs against Polly's own coverage.config.ts.
 */
async function coverage() {
  const monorepoMarker = `${__dirname}/../scripts/coverage.config.ts`;
  const sourceCli = `${__dirname}/../tools/test/src/coverage-policy/cli.ts`;
  const bundledCli = `${__dirname}/../tools/test/src/coverage-policy/cli.js`;

  const isMonorepo = await Bun.file(monorepoMarker).exists();
  let cliPath = sourceCli;
  if (!isMonorepo && (await Bun.file(bundledCli).exists())) {
    cliPath = bundledCli;
  }

  const args = [...commandArgs];
  if (isMonorepo) {
    // Polly's config lives under scripts/, and its polly.mutate.ts sits at the
    // monorepo root (checked separately by `polly check`).
    args.unshift("--config", "scripts/coverage.config.ts", "--no-mutate");
  }

  const exitCode = await runChild(["bun", cliPath, ...args], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Coverage check failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Test command - delegate to @fairfox/polly-test
 */
async function test() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/test/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/test/src/cli.ts`;
  const testCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", testCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Tests failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Browser test command — bundles *.browser.{ts,tsx} files, serves them,
 * opens a Puppeteer page, and collects results. Consumers use this to
 * run tests written with @fairfox/polly/test/browser in a real browser.
 */
async function testBrowser() {
  const bundledCli = `${__dirname}/../tools/test/src/browser/run.js`;
  const monorepoCli = `${__dirname}/../tools/test/src/browser/run.ts`;
  const browserCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", browserCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Browser tests failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Check command - run all quality checks in sequence
 */
async function check() {
  const checks = [
    { name: "Type checking", fn: typecheck },
    { name: "Linting", fn: lint },
    { name: "Testing", fn: test },
    { name: "Building", fn: build },
    { name: "Verification", fn: verify, optional: true },
    { name: "Visualization", fn: visualize, optional: true },
  ];

  for (const { name, fn, optional } of checks) {
    try {
      await fn();
    } catch (error) {
      // A signalled child (Ctrl-C, SIGTERM) stops the whole run, optional or not.
      if (error instanceof ChildExitError && error.exitCode > 128) {
        throw error;
      }
      if (optional) {
        continue;
      }
      console.log(`\n\x1b[31m✗ ${name} failed\x1b[0m\n`);
      process.exit(1);
    }
  }
}

/**
 * Init command - delegate to @fairfox/polly-init
 */
async function init() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/init/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/init/src/cli.ts`;
  const initCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const exitCode = await runChild(["bun", initCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });
  if (exitCode !== 0) {
    throw new ChildExitError(`Initialization failed with exit code ${exitCode}`, exitCode);
  }
}

/**
 * Help command — prints usage from the docstring at the top of this file
 */
function help() {
  console.log(`Polly CLI — multi-execution-context framework

Usage:
  polly init [name] [--type=TYPE]  Create a new project
  polly check                      Run all checks (typecheck, lint, test, build)
  polly build [options]            Build the project
  polly dev                        Build with watch mode
  polly typecheck                  Type check your code
  polly lint [--fix]               Lint your code
  polly format                     Format your code
  polly test [args]                Run tests (bun test)
  polly test --tier=T | --all | --full | --list
                                   Run the multi-tier suite (unit → integration
                                   → browser → e2e → verify) with timed reports
  polly test:browser [dir]         Run *.browser.{ts,tsx} in Puppeteer
  polly coverage [flags]           Per-file coverage policy, orphan detection,
                                   and mutate-target validation (zero-config)
  polly mutate [init|run|report|verify] Mutation testing + useless/redundant-test detection
  polly mutate decisions [decide]  Review/record verdicts on subsumed tests
  polly verify [args]              Run formal verification
  polly bdd [run|check|new]        Executable Gherkin across the real boundary,
                                   cross-checked against the verification config
  polly visualize [args]           Generate architecture diagrams
  polly gallery [--port|--build|--open] Serve/export the polly-ui component gallery
  polly quality [args]             Run quality conformance checks
  polly help                       Show this help

Options:
  --prod              Build for production (minified)
  --config <path>     Path to config file (default: polly.config.ts)
  --fix               Auto-fix lint/format issues
  --type=TYPE         Project type for init command (pwa, extension, websocket, generic)`);
}

/**
 * Main entry point
 */
async function main() {
  try {
    switch (command) {
      case "init":
        await init();
        break;
      case "check":
        await check();
        break;
      case "build":
        await build();
        break;
      case "dev":
        await dev();
        break;
      case "typecheck":
        await typecheck();
        break;
      case "lint":
        await lint();
        break;
      case "format":
        await format();
        break;
      case "test":
        if (isTierMode(commandArgs)) {
          await testTiers();
        } else {
          await test();
        }
        break;
      case "test:browser":
        await testBrowser();
        break;
      case "coverage":
        await coverage();
        break;
      case "mutate":
        await mutate();
        break;
      case "verify":
        await verify();
        break;
      case "bdd":
        await bdd();
        break;
      case "visualize":
        await visualize();
        break;
      case "gallery":
        await gallery();
        break;
      case "quality":
        await quality();
        break;
      case "help":
      case "--help":
      case "-h":
      case undefined:
        help();
        break;
      default:
        console.log(`❌ Unknown command: ${command}\n`);
        help();
        process.exit(1);
    }
  } catch (error) {
    if (error instanceof ChildExitError) {
      // The child already reported its own failure; relay its status. A
      // signalled child (exit > 128) was stopped on purpose, so stay quiet.
      if (error.exitCode <= 128) console.log(`\n❌ Command failed: ${error.message}`);
      process.exit(error.exitCode);
    }
    console.log("\n❌ Command failed:", error);
    process.exit(1);
  }
}

main();
