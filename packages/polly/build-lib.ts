#!/usr/bin/env bun
// biome-ignore lint/suspicious/noConsoleLog: Build script needs console output

/**
 * Build script for npm library publishing
 *
 * This script:
 * 1. Compiles ALL TypeScript (src + cli + vendor) to JavaScript ESM in dist/
 * 2. Generates TypeScript declaration files (.d.ts)
 * 3. Bundles vendor tools with all dependencies inline
 */

import { existsSync, rmSync } from "node:fs";
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
  entrypoints: ["cli/polly.ts", "vendor/verify/src/cli.ts", "vendor/visualize/src/cli.ts"],
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
      rootDir: "src",
    },
    include: ["src/**/*"],
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
