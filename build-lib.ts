#!/usr/bin/env bun
// biome-ignore lint/suspicious/noConsoleLog: Build script needs console output

/**
 * Build script for npm library publishing
 *
 * This script:
 * 1. Compiles ALL TypeScript (src + cli + tools) to JavaScript ESM in dist/
 * 2. Generates TypeScript declaration files (.d.ts)
 * 3. Bundles tools with all dependencies inline
 */

import { existsSync, rmSync, cpSync, mkdirSync } from "node:fs";
import { join } from "node:path";
import { $ } from "bun";

const DIST_DIR = "dist";

// Clean dist directory
if (existsSync(DIST_DIR)) {
  rmSync(DIST_DIR, { recursive: true, force: true });
}

console.log("🔨 Building library (browser target)...");

// Build main library (browser target)
const libResult = await Bun.build({
  entrypoints: [
    // Main entry point
    "src/index.ts",

    // Individual module exports
    "src/shared/lib/state.ts",
    "src/shared/lib/message-bus.ts",
    "src/shared/lib/errors.ts",
    "src/shared/lib/context-helpers.ts",
    "src/shared/lib/test-helpers.ts",
    "src/shared/adapters/index.ts",
    "src/shared/types/messages.ts",
    "src/shared/state/app-state.ts",
    "src/background/index.ts",
    "src/background/message-router.ts",

    // Verify tool config helper (lightweight, no heavy deps)
    "tools/verify/src/config.ts",
  ],
  outdir: DIST_DIR,
  target: "browser",
  format: "esm",
  splitting: false,
  minify: false,
  sourcemap: "external",
  naming: {
    entry: "[dir]/[name].[ext]",
  },
  external: ["preact", "@preact/signals"],
});

if (!libResult.success) {
  console.error("❌ Library build failed:");
  for (const log of libResult.logs) {
    console.error(log);
  }
  process.exit(1);
}

console.log("✅ Library built");
console.log("🔨 Building CLI and tools (node target, fully bundled)...");

// Build CLI and tools (node target) - bundle EVERYTHING
const toolsResult = await Bun.build({
  entrypoints: [
    "cli/polly.ts",
    "cli/template-utils.ts",
    "tools/verify/src/cli.ts",
    "tools/visualize/src/cli.ts",
    "tools/teach/src/cli.ts",
    "scripts/build-extension.ts",
  ],
  outdir: DIST_DIR,
  target: "node",
  format: "esm",
  splitting: false,
  minify: false,
  sourcemap: "external",
  naming: {
    entry: "[dir]/[name].[ext]",
  },
  external: ["ts-morph", "bun:*", "node:*"],
});

if (!toolsResult.success) {
  console.error("❌ Tools build failed:");
  for (const log of toolsResult.logs) {
    console.error(log);
  }
  process.exit(1);
}

console.log("✅ Tools built");
console.log("🔨 Copying specs for verification tool...");

// Copy MessageRouter.tla specs to dist so verify CLI can find them
const specsSourceDir = join("tools", "verify", "specs");
const specsDestDir = join(DIST_DIR, "tools", "verify", "specs");

mkdirSync(specsDestDir, { recursive: true });
cpSync(specsSourceDir, specsDestDir, { recursive: true });

console.log("✅ Specs copied");
console.log("🔨 Generating TypeScript declarations...");

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
    },
    include: ["src/**/*", "tools/verify/src/config.ts"],
    exclude: [
      "src/content/**/*",
      "src/devtools/**/*",
      "src/options/**/*",
      "src/popup/**/*",
      "src/offscreen/**/*",
      "src/page/**/*",
      "src/ui/**/*",
      "**/*.test.ts",
      "**/*.spec.ts",
    ],
  };

  await Bun.write(tsconfigPath, JSON.stringify(tsconfigContent, null, 2));
  await $`bunx tsc --project ${tsconfigPath}`;
  rmSync(tsconfigPath);
  console.log("✅ Declarations generated");
} catch (error) {
  console.error("❌ Failed to generate TypeScript declarations");
  console.error(error);
  process.exit(1);
}

console.log("\n✨ Build complete!");
