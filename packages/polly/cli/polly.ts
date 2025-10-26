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
 *   polly init [name]            Create a new project
 *   polly check                  Run all checks (typecheck, lint, test, build)
 *   polly build [options]        Build the project
 *   polly dev                    Build with watch mode
 *   polly typecheck              Type check your code
 *   polly lint [--fix]           Lint your code
 *   polly format                 Format your code
 *   polly test [args]            Run tests (requires bun test)
 *   polly verify [args]          Run formal verification
 *   polly visualize [args]       Generate architecture diagrams
 *   polly help                   Show help
 *
 * Options:
 *   --prod              Build for production (minified)
 *   --config <path>     Path to config file (default: polly.config.ts)
 *   --fix               Auto-fix lint/format issues
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
  ].filter(Boolean) as string[];

  for (const configPath of configPaths) {
    // Use Bun.file().exists() instead of existsSync
    if (await Bun.file(configPath).exists()) {
      try {
        const config = await import(configPath);
        return config.default || config;
      } catch (error) {
        console.error(`❌ Failed to load config: ${configPath}`);
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
      console.error(`\n\x1b[31m✗ ${name} failed\x1b[0m\n`);
      process.exit(1);
    }
  }
}

/**
 * Init command - scaffold a new extension
 */
async function init() {
  const projectName = commandArgs[0] || "my-extension";
  const projectPath = `${cwd}/${projectName}`;

  // Check if directory already exists
  const { existsSync, mkdirSync, writeFileSync } = await import("node:fs");

  if (existsSync(projectPath)) {
    console.error(`\x1b[31m✗ Directory '${projectName}' already exists\x1b[0m\n`);
    process.exit(1);
  }

  // Create project structure
  const dirs = [
    projectPath,
    `${projectPath}/src`,
    `${projectPath}/src/background`,
    `${projectPath}/src/popup`,
  ];

  for (const dir of dirs) {
    mkdirSync(dir, { recursive: true });
  }

  // Create package.json
  const packageJson = {
    name: projectName,
    version: "0.1.0",
    type: "module",
    scripts: {
      check: "web-ext check",
      build: "web-ext build",
      "build:prod": "web-ext build --prod",
      typecheck: "web-ext typecheck",
      lint: "web-ext lint",
      "lint:fix": "web-ext lint --fix",
      format: "web-ext format",
      test: "web-ext test",
      verify: "web-ext verify",
      "verify:setup": "web-ext verify --setup",
      visualize: "web-ext visualize",
      "visualize:export": "web-ext visualize --export",
      "visualize:serve": "web-ext visualize --serve",
    },
    dependencies: {
      "@fairfox/web-ext": "*",
    },
  };

  writeFileSync(`${projectPath}/package.json`, JSON.stringify(packageJson, null, 2));

  // Create manifest.json at root
  const manifest = {
    manifest_version: 3,
    name: projectName,
    version: "0.1.0",
    description: "A Chrome extension built with @fairfox/web-ext",
    background: {
      service_worker: "background/index.js",
      type: "module",
    },
    action: {
      default_popup: "popup/popup.html",
    },
    permissions: ["storage"],
  };

  writeFileSync(`${projectPath}/manifest.json`, JSON.stringify(manifest, null, 2));

  // Create background script
  const backgroundScript = `/**
 * Background Service Worker
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";
import { MessageRouter } from "@fairfox/web-ext/message-router";

const bus = getMessageBus("background");
new MessageRouter(bus);

// Add your message handlers here
bus.on("PING", async () => {
  return { success: true, message: "pong" };
});

console.log("Background service worker initialized");
`;

  writeFileSync(`${projectPath}/src/background/index.ts`, backgroundScript);

  // Create popup HTML in src/popup
  const popupHtml = `<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8" />
    <title>${projectName}</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="./index.js"></script>
  </body>
</html>
`;

  writeFileSync(`${projectPath}/src/popup/popup.html`, popupHtml);

  // Create popup script
  const popupScript = `/**
 * Popup UI
 */

import { getMessageBus } from "@fairfox/web-ext/message-bus";

const bus = getMessageBus("popup");

// Simple example without UI framework
const root = document.getElementById("root");

if (root) {
  root.innerHTML = \`
    <div style="padding: 16px; min-width: 200px;">
      <h1 style="margin: 0 0 8px 0; font-size: 18px;">${projectName}</h1>
      <button id="ping-btn" style="padding: 8px 16px;">Ping Background</button>
      <p id="response" style="margin-top: 8px; font-size: 14px;"></p>
    </div>
  \`;

  const btn = document.getElementById("ping-btn");
  const response = document.getElementById("response");

  btn?.addEventListener("click", async () => {
    const result = await bus.send({ type: "PING" });
    if (response) {
      response.textContent = JSON.stringify(result);
    }
  });
}
`;

  writeFileSync(`${projectPath}/src/popup/index.ts`, popupScript);

  // Create tsconfig.json
  const tsconfig = {
    compilerOptions: {
      target: "ES2022",
      module: "ESNext",
      lib: ["ES2022", "DOM"],
      moduleResolution: "bundler",
      strict: true,
      esModuleInterop: true,
      skipLibCheck: true,
      forceConsistentCasingInFileNames: true,
      resolveJsonModule: true,
      allowSyntheticDefaultImports: true,
      jsx: "react-jsx",
      jsxImportSource: "preact",
    },
    include: ["src/**/*"],
  };

  writeFileSync(`${projectPath}/tsconfig.json`, JSON.stringify(tsconfig, null, 2));

  // Create biome.json
  const biomeConfig = {
    files: {
      includes: ["src/**/*.ts", "src/**/*.tsx"],
      ignoreUnknown: true,
    },
    linter: {
      enabled: true,
      rules: {
        recommended: true,
      },
    },
    formatter: {
      enabled: true,
      indentStyle: "space",
      indentWidth: 2,
    },
  };

  writeFileSync(`${projectPath}/biome.json`, JSON.stringify(biomeConfig, null, 2));

  // Create README
  const readme = `# ${projectName}

A Chrome extension built with [@fairfox/web-ext](https://github.com/fairfox/web-ext).

## Getting Started

1. Install dependencies:
   \`\`\`bash
   bun install
   \`\`\`

2. Build the extension:
   \`\`\`bash
   bun run build
   \`\`\`

3. Load the extension in Chrome:
   - Open \`chrome://extensions\`
   - Enable "Developer mode"
   - Click "Load unpacked"
   - Select the \`dist/\` folder

## Development

- \`bun run build\` - Build the extension
- \`bun run check\` - Run all checks (typecheck, lint, test, build)
- \`bun run typecheck\` - Type check your code
- \`bun run lint\` - Lint your code
- \`bun run format\` - Format your code
- \`bun run verify\` - Run formal verification
- \`bun run visualize\` - Generate architecture diagrams

## Project Structure

\`\`\`
${projectName}/
├── src/
│   ├── background/
│   │   └── index.ts    # Background service worker
│   └── popup/
│       ├── popup.html  # Popup HTML
│       └── index.ts    # Popup script
├── manifest.json       # Extension manifest
├── dist/               # Build output (load this in Chrome)
├── package.json
├── tsconfig.json
└── biome.json
\`\`\`
`;

  writeFileSync(`${projectPath}/README.md`, readme);

  // Create .gitignore
  const gitignore = `node_modules
dist
docs
.DS_Store
`;

  writeFileSync(`${projectPath}/.gitignore`, gitignore);
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
        console.error(`❌ Unknown command: ${command}\n`);
        help();
        process.exit(1);
    }
  } catch (error) {
    console.error("\n❌ Command failed:", error);
    process.exit(1);
  }
}

main();
