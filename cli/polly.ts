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
 *   polly verify [args]              Run formal verification
 *   polly visualize [args]           Generate architecture diagrams
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

import { existsSync } from "node:fs";
import {
  type ProjectType,
  getTemplateDir,
  scaffoldFromTemplate,
  validateProjectName,
} from "./template-utils";

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
  ].filter(Boolean) as string[];

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
  const bundledCli = `${__dirname}/../vendor/verify/src/cli.js`;
  const monorepoCli = `${__dirname}/../../verify/src/cli.ts`;
  const verifyCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", verifyCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Verification failed with exit code ${exitCode}`);
  }
}

/**
 * Visualize command - delegate to @fairfox/polly-visualize
 */
async function visualize() {
  // Check if bundled (published) or in monorepo
  const bundledCli = `${__dirname}/../vendor/visualize/src/cli.js`;
  const monorepoCli = `${__dirname}/../../visualize/src/cli.ts`;
  const visualizeCli = (await Bun.file(bundledCli).exists()) ? bundledCli : monorepoCli;

  const proc = Bun.spawn(["bun", visualizeCli, ...commandArgs], {
    cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    throw new Error(`Visualization failed with exit code ${exitCode}`);
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

/**
 * Test command - run Bun tests
 */
async function test() {
  const proc = Bun.spawn(["bun", "test", ...commandArgs], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
    stdin: "inherit",
  });

  const stdout = await new Response(proc.stdout).text();
  const stderr = await new Response(proc.stderr).text();

  // Output the results
  if (stdout) process.stdout.write(stdout);
  if (stderr) process.stderr.write(stderr);

  const exitCode = await proc.exited;

  // Check if no tests were found (not a failure)
  if (stderr.includes("0 test files matching")) {
    return;
  }

  if (exitCode !== 0) {
    throw new Error(`Tests failed with exit code ${exitCode}`);
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
 * Init command - scaffold a new project
 */
async function init() {
  // Parse arguments
  const projectName = commandArgs[0] || "my-project";
  const typeArg =
    commandArgs.find((arg) => arg.startsWith("--type="))?.split("=")[1] || "extension";
  const projectType = typeArg as ProjectType;

  // Validate project name
  const validation = validateProjectName(projectName);
  if (!validation.valid) {
    console.log(`\x1b[31m✗ ${validation.error}\x1b[0m\n`);
    process.exit(1);
  }

  const projectPath = `${cwd}/${projectName}`;

  // Check if directory already exists
  if (existsSync(projectPath)) {
    console.log(`\x1b[31m✗ Directory '${projectName}' already exists\x1b[0m\n`);
    process.exit(1);
  }

  // Get template directory
  const templateDir = getTemplateDir(projectType, __dirname);

  // Scaffold project
  await scaffoldFromTemplate({
    projectName,
    projectPath,
    projectType,
    templateDir,
  });
}

/**
 * Help command
 */
function help() {
  // Help is shown automatically via commander
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
        await test();
        break;
      case "verify":
        await verify();
        break;
      case "visualize":
        await visualize();
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
