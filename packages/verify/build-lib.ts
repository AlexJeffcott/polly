#!/usr/bin/env bun

/**
 * Build script for @fairfox/web-ext-verify npm publishing
 *
 * This script:
 * 1. Compiles TypeScript source to JavaScript ESM in dist/
 * 2. Generates TypeScript declaration files (.d.ts)
 * 3. Makes the CLI executable
 */

import { cpSync, existsSync, rmSync, chmodSync } from "node:fs";
import { join } from "node:path";
import { $ } from "bun";

const DIST_DIR = "dist";
const TEMP_DIR = "dist-temp";

console.log("🏗️  Building @fairfox/web-ext-verify library...\n");

// Clean dist directory
if (existsSync(DIST_DIR)) {
  console.log("🧹 Cleaning dist directory...");
  rmSync(DIST_DIR, { recursive: true, force: true });
}

if (existsSync(TEMP_DIR)) {
  rmSync(TEMP_DIR, { recursive: true, force: true });
}

// Build JavaScript with Bun
console.log("📦 Building JavaScript...");
const buildResult = await Bun.build({
  entrypoints: [
    // Main entry point
    "src/index.ts",

    // CLI entry point
    "src/cli.ts",
  ],
  outdir: TEMP_DIR,
  target: "node", // CLI runs in Node/Bun
  format: "esm",
  splitting: false,
  minify: false,
  sourcemap: "external",
  naming: {
    entry: "[dir]/[name].[ext]",
  },
  root: "src",
  external: [
    // Mark dependencies as external (they'll be installed by users)
    "ts-morph",
    "chokidar",
    "chalk",
  ],
});

if (!buildResult.success) {
  console.error("❌ Build failed:");
  for (const log of buildResult.logs) {
    console.error(log);
  }
  process.exit(1);
}

console.log(`✅ Built ${buildResult.outputs.length} files`);

// Move files from dist-temp/src/ to dist/
console.log("\n📦 Restructuring output...");
const tempSrcDir = join(TEMP_DIR, "src");
if (existsSync(tempSrcDir)) {
  cpSync(tempSrcDir, DIST_DIR, { recursive: true });
} else {
  cpSync(TEMP_DIR, DIST_DIR, { recursive: true });
}
rmSync(TEMP_DIR, { recursive: true, force: true });
console.log("✅ Output restructured");

// Generate TypeScript declarations
console.log("\n📝 Generating TypeScript declarations...");
try {
  // Use a custom tsconfig for declaration generation
  const tsconfigPath = "tsconfig.lib.json";
  const tsconfigContent = {
    extends: "./tsconfig.json",
    compilerOptions: {
      declaration: true,
      emitDeclarationOnly: true,
      outDir: "dist",
      skipLibCheck: true,
      noEmit: false,
      rootDir: "src",
    },
    include: ["src/**/*"],
    exclude: [
      "src/**/*.test.ts",
      "src/**/*.spec.ts",
    ],
  };

  await Bun.write(tsconfigPath, JSON.stringify(tsconfigContent, null, 2));
  await $`bunx tsc --project ${tsconfigPath}`;
  rmSync(tsconfigPath);
  console.log("✅ TypeScript declarations generated");
} catch (error) {
  console.error("❌ Failed to generate TypeScript declarations");
  console.error(error);
  process.exit(1);
}

// Make CLI executable
console.log("\n🔧 Making CLI executable...");
const cliPath = join(DIST_DIR, "cli.js");
if (existsSync(cliPath)) {
  // Read CLI file and remove any existing shebangs, then add Node shebang
  let cliContent = await Bun.file(cliPath).text();

  // Remove all shebang lines (lines starting with #!)
  const lines = cliContent.split('\n');
  const filteredLines = lines.filter(line => !line.startsWith('#!'));

  // Add proper Node.js shebang at the top
  const cliWithShebang = `#!/usr/bin/env node\n${filteredLines.join('\n')}`;
  await Bun.write(cliPath, cliWithShebang);

  // Make executable on Unix systems
  try {
    chmodSync(cliPath, 0o755);
  } catch (e) {
    // chmod may fail on Windows, that's ok
  }
  console.log("✅ CLI is executable");
} else {
  console.warn("⚠️  CLI file not found at expected location");
}

console.log("\n✨ Build complete! Library ready for publishing.\n");
