#!/usr/bin/env bun
/**
 * web-ext CLI
 *
 * Command-line tool for building Chrome extensions with the web-ext framework.
 *
 * Usage:
 *   web-ext build [options]
 *   web-ext dev
 *   web-ext help
 *
 * Options:
 *   --prod              Build for production (minified)
 *   --config <path>     Path to config file (default: web-ext.config.ts)
 */

// Use Bun built-ins instead of Node.js APIs
const __dirname = import.meta.dir;

const command = process.argv[2];
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
    `${cwd}/web-ext.config.ts`,
    `${cwd}/web-ext.config.js`,
    `${cwd}/web-ext.config.mjs`,
  ].filter(Boolean) as string[];

  for (const configPath of configPaths) {
    // Use Bun.file().exists() instead of existsSync
    if (await Bun.file(configPath).exists()) {
      try {
        const config = await import(configPath);
        console.log(`📝 Loaded config: ${configPath}`);
        return config.default || config;
      } catch (error) {
        console.error(`❌ Failed to load config: ${configPath}`);
        throw error;
      }
    }
  }

  // Default config
  console.log("📝 Using default config");
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
  console.log(`\n🏗️  Building extension...`);
  console.log(`Mode: ${args.prod ? "production" : "development"}\n`);

  const config = await loadConfig();

  // Import the build script from framework
  const buildScriptPath = `${__dirname}/../scripts/build-extension.ts`;

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
    env: process.env as Record<string, string>,
  });

  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    process.exit(exitCode);
  }

  console.log("\n✅ Build complete!\n");
}

/**
 * Dev command - build with watch mode
 */
async function dev() {
  console.log("\n👀 Starting dev mode with watch...\n");

  // TODO: Implement watch mode
  console.log("⚠️  Watch mode not yet implemented");
  console.log("For now, run: web-ext build");

  await build();
}

/**
 * Help command
 */
function help() {
  console.log(`
web-ext - Chrome Extension Framework CLI

USAGE:
  web-ext <command> [options]

COMMANDS:
  build              Build the extension
  dev                Build with watch mode (coming soon)
  help               Show this help message

OPTIONS:
  --prod             Build for production (minified, no sourcemaps)
  --config <path>    Path to config file (default: web-ext.config.ts)

EXAMPLES:
  web-ext build
  web-ext build --prod
  web-ext dev
  web-ext build --config my-config.ts

CONFIGURATION:
  Create a web-ext.config.ts file in your project root:

  export default {
    srcDir: 'src',
    distDir: 'dist',
    manifest: 'manifest.json',
  }

LEARN MORE:
  Documentation: https://github.com/fairfox/web-ext
`);
}

/**
 * Main entry point
 */
async function main() {
  try {
    switch (command) {
      case "build":
        await build();
        break;
      case "dev":
        await dev();
        break;
      case "help":
      case "--help":
      case "-h":
        help();
        break;
      default:
        console.error(`❌ Unknown command: ${command}\n`);
        help();
        process.exit(1);
    }
  } catch (error) {
    console.error("\n❌ Build failed:", error);
    process.exit(1);
  }
}

main();
