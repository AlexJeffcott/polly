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
 *   polly coverage [flags]           Coverage policy + orphan + Stryker checks
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

/**
 * Load user's configuration
 */
async function loadConfig() {
  const configPaths = [
    args.config,
    `${cwd}/polly.config.ts`,
    `${cwd}/polly.config.js`,
    `${cwd}/polly.config.mjs`,
  ].filter(Boolean) as unknown as string[];

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
  const proc = Bun.spawn(["bun", buildScriptPath], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });

  const exitCode = await proc.exited;
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
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/verify/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/verify/src/cli.ts`;
  const verifyCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", verifyCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Verification failed with exit code ${exitCode}`);
  }
}

/**
 * Mutate command - delegate to tools/mutate (Stryker + useless-test detection)
 */
async function mutate() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/mutate/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/mutate/src/cli.ts`;
  const mutateCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  // Pass the full commandArgs through — the tool's own cli reads the subcommand
  // (run/report/decisions/verify) as its first positional.
  const proc = Bun.spawn(["bun", mutateCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Mutation testing failed with exit code ${exitCode}`);
  }
}

/**
 * BDD command - delegate to tools/bdd (executable Gherkin against the model)
 */
async function bdd() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/bdd/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/bdd/src/cli.ts`;
  const bddCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  // Pass the full commandArgs through — the tool's own cli reads the subcommand
  // (run/check/new) as its first positional.
  const proc = Bun.spawn(["bun", bddCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`BDD run failed with exit code ${exitCode}`);
  }
}

/**
 * Visualize command - delegate to @fairfox/polly-visualize
 */
async function visualize() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../tools/visualize/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/visualize/src/cli.ts`;
  const visualizeCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", visualizeCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Visualization failed with exit code ${exitCode}`);
  }
}

/**
 * Gallery command - delegate to tools/gallery (serve/export the polly-ui gallery)
 */
async function gallery() {
  const bundledCli = `${__dirname}/../tools/gallery/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/gallery/src/cli.ts`;
  const galleryCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", galleryCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Gallery failed with exit code ${exitCode}`);
  }
}

/**
 * Quality command - delegate to @fairfox/polly-quality
 */
async function quality() {
  const bundledCli = `${__dirname}/../tools/quality/src/cli.js`;
  const monorepoCli = `${__dirname}/../tools/quality/src/cli.ts`;
  const qualityCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", qualityCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Quality checks failed with exit code ${exitCode}`);
  }
}

/**
 * Typecheck command - run TypeScript type checking
 */
async function typecheck() {
  const proc = Bun.spawn(["bunx", "tsc", "--noEmit"], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Type checking failed with exit code ${exitCode}`);
  }
}

/**
 * Lint command - run Biome linter
 */
async function lint() {
  const fix = commandArgs.includes("--fix");
  const lintArgs = fix ? ["check", "--write", "."] : ["check", "."];

  const proc = Bun.spawn(["bunx", "@biomejs/biome", ...lintArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Linting failed with exit code ${exitCode}`);
  }
}

/**
 * Format command - run Biome formatter
 */
async function format() {
  const proc = Bun.spawn(["bunx", "@biomejs/biome", "format", "--write", "."], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Formatting failed with exit code ${exitCode}`);
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

  const proc = Bun.spawn(["bun", runnerCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Tiered tests failed with exit code ${exitCode}`);
  }
}

/**
 * Coverage command — per-file coverage policy, orphan detection, and Stryker
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
    // Polly's config lives under scripts/, and its Stryker config sits at the
    // monorepo root (checked separately by `polly check`).
    args.unshift("--config", "scripts/coverage.config.ts", "--no-mutate");
  }

  const proc = Bun.spawn(["bun", cliPath, ...args], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Coverage check failed with exit code ${exitCode}`);
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

  const proc = Bun.spawn(["bun", testCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Tests failed with exit code ${exitCode}`);
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

  const proc = Bun.spawn(["bun", browserCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Browser tests failed with exit code ${exitCode}`);
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
    } catch (_error) {
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

  const proc = Bun.spawn(["bun", initCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Initialization failed with exit code ${exitCode}`);
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
                                   and Stryker target validation (zero-config)
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
    console.log("\n❌ Command failed:", error);
    process.exit(1);
  }
}

main();
