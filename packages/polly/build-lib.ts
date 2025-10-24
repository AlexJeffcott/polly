#!/usr/bin/env bun

/**
 * Build script for npm library publishing
 *
 * This script:
 * 1. Compiles TypeScript source to JavaScript ESM in dist/
 * 2. Generates TypeScript declaration files (.d.ts)
 * 3. Preserves the module structure for proper exports
 */

import { cpSync, existsSync, rmSync } from "node:fs";
import { join } from "node:path";
import { $ } from "bun";

const DIST_DIR = "dist";
const TEMP_DIR = "dist-temp";

// Clean dist directory
if (existsSync(DIST_DIR)) {
  rmSync(DIST_DIR, { recursive: true, force: true });
}

if (existsSync(TEMP_DIR)) {
  rmSync(TEMP_DIR, { recursive: true, force: true });
}
const buildResult = await Bun.build({
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
  outdir: TEMP_DIR,
  target: "browser",
  format: "esm",
  splitting: false, // Disable splitting for simpler output structure
  minify: false, // Keep readable for library consumers
  sourcemap: "external",
  naming: {
    entry: "[dir]/[name].[ext]",
  },
  root: "src",
  external: [
    // Mark peer dependencies and platform APIs as external
    "preact",
    "@preact/signals",
  ],
});

if (!buildResult.success) {
  console.error("❌ Build failed:");
  for (const log of buildResult.logs) {
    console.error(log);
  }
  process.exit(1);
}
const tempSrcDir = join(TEMP_DIR, "src");
if (existsSync(tempSrcDir)) {
  cpSync(tempSrcDir, DIST_DIR, { recursive: true });
} else {
  cpSync(TEMP_DIR, DIST_DIR, { recursive: true });
}
rmSync(TEMP_DIR, { recursive: true, force: true });
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
} catch (error) {
  console.error("❌ Failed to generate TypeScript declarations");
  console.error(error);
  process.exit(1);
}
