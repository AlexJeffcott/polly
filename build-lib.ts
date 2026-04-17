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
    "src/shared/lib/resource.ts",
    "src/shared/lib/message-bus.ts",
    "src/shared/lib/errors.ts",
    "src/shared/lib/context-helpers.ts",
    "src/shared/lib/test-helpers.ts",
    "src/shared/adapters/index.ts",
    "src/shared/types/messages.ts",
    "src/shared/state/app-state.ts",
    "src/background/index.ts",
    "src/background/message-router.ts",

    // Peer-first and mesh state (isolated subpath exports)
    "src/peer.ts",
    "src/mesh.ts",
    "src/mesh-node.ts",

    // Elysia integration
    "src/elysia/index.ts",
    "src/client/index.ts",

    // Actions subpath (event delegation, action registry, form primitive)
    "src/actions/index.ts",

    // UI primitives subpath
    "src/polly-ui/index.ts",

    // Tool exports
    "tools/verify/src/config.ts",
    "tools/test/src/index.ts",
    "tools/test/src/test-utils.ts",
    "tools/test/src/browser/index.ts",
    "tools/test/src/visual/index.ts",
    "tools/test/src/adapters/index.ts",
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
  external: [
    "preact",
    "@preact/signals",
    "elysia",
    "@elysiajs/eden",
    "serialize-javascript",
    "@automerge/automerge",
    "@automerge/automerge/automerge.wasm",
    "@automerge/automerge-repo",
    "@automerge/automerge-repo/slim",
    "@automerge/automerge-repo-network-websocket",
    "@automerge/automerge-repo-storage-indexeddb",
    "@automerge/automerge-repo-storage-nodefs",
    "ws",
    "tweetnacl",
    "bun",
    "puppeteer",
    "werift",
    "@roamhq/wrtc",
    "node:fs/promises",
    "node:readline/promises",
  ],
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
    "tools/init/src/cli.ts",
    "tools/verify/src/cli.ts",
    "tools/visualize/src/cli.ts",
    "tools/test/src/cli.ts",
    "tools/test/src/browser/run.ts",
    "tools/quality/src/cli.ts",
    "tools/quality/src/index.ts",
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
  external: [
    "ts-morph",
    "bun",
    "bun:*",
    "node:*",
    "elysia",
    "@elysiajs/*",
    "puppeteer",
    "ws",
    "@automerge/*",
    "werift",
    "@roamhq/wrtc",
    "tweetnacl",
    "pixelmatch",
    "pngjs",
  ],
});

if (!toolsResult.success) {
  console.error("❌ Tools build failed:");
  for (const log of toolsResult.logs) {
    console.error(log);
  }
  process.exit(1);
}

console.log("✅ Tools built");
console.log("🔨 Copying templates for init tool...");

// Copy templates to dist so init CLI can find them
const templatesSourceDir = join("tools", "init", "templates");
const templatesDestDir = join(DIST_DIR, "tools", "init", "templates");

mkdirSync(templatesDestDir, { recursive: true });
cpSync(templatesSourceDir, templatesDestDir, { recursive: true });

console.log("✅ Templates copied");
console.log("🔨 Copying UI stylesheets...");

const pollyUiSrc = join("src", "polly-ui");
const pollyUiDest = join(DIST_DIR, "src", "polly-ui");
mkdirSync(pollyUiDest, { recursive: true });
for (const file of ["styles.css", "theme.css"]) {
  await Bun.write(join(pollyUiDest, file), await Bun.file(join(pollyUiSrc, file)).text());
}

console.log("✅ UI stylesheets copied");
console.log("🔨 Copying specs for verification tool...");

// Copy MessageRouter.tla specs to dist so verify CLI can find them
const specsSourceDir = join("tools", "verify", "specs");
const specsDestDir = join(DIST_DIR, "tools", "verify", "specs");

mkdirSync(specsDestDir, { recursive: true });
cpSync(specsSourceDir, specsDestDir, { recursive: true });

console.log("✅ Specs copied");
console.log("🔨 Copying Dockerfile for verification tool...");

// Copy Dockerfile to dist so verify CLI can build Docker image
const dockerfileSourcePath = join("tools", "verify", "Dockerfile");
const dockerfileDestPath = join(DIST_DIR, "tools", "verify", "Dockerfile");

await Bun.write(dockerfileDestPath, await Bun.file(dockerfileSourcePath).text());

console.log("✅ Dockerfile copied");
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
      rootDir: ".",
      skipLibCheck: true,
      noEmit: false,
    },
    include: [
      "src/**/*",
      "tools/verify/src/config.ts",
      "tools/test/src/**/*",
      "tools/quality/src/index.ts",
      "tools/quality/src/no-as-casting.ts",
      "tools/quality/src/logger.ts",
      "tools/quality/src/css/**/*",
    ],
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
