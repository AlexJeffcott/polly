#!/usr/bin/env bun
/**
 * Build Script for User Extensions
 *
 * This script can be copied by users to build their own extensions
 * that import and use the web-ext framework.
 *
 * Usage:
 *   bun run build-user-extension.ts [path-to-extension]
 *
 * Example:
 *   bun run build-user-extension.ts examples/full-featured
 */

// ============================================================================
// Configuration
// ============================================================================

const args = process.argv.slice(2);
const extensionPath = args[0] || "examples/full-featured";
const isProd = args.includes("--prod");

const srcDir = `${extensionPath}/src`;
const distDir = `${extensionPath}/dist`;

console.log(`Building extension: ${extensionPath}`);
console.log(`Mode: ${isProd ? "production" : "development"}`);

// ============================================================================
// Helper Functions
// ============================================================================

async function cleanDist() {
  // Use Bun shell for directory operations
  await Bun.$`rm -rf ${distDir}`.quiet();
  await Bun.$`mkdir -p ${distDir}`.quiet();
}

async function copyManifest() {
  const manifestPath = `${extensionPath}/manifest.json`;
  if (!(await Bun.file(manifestPath).exists())) {
    throw new Error("manifest.json not found");
  }

  const manifest = await Bun.file(manifestPath).json();
  await Bun.write(`${distDir}/manifest.json`, JSON.stringify(manifest, null, 2));

  console.log("✓ Copied manifest.json");
}

async function copyHTML() {
  const htmlFiles = [
    "popup/popup.html",
    "options/options.html",
    "devtools/devtools.html",
    "devtools/panel.html",
    "offscreen/offscreen.html",
  ];

  for (const file of htmlFiles) {
    const srcPath = `${srcDir}/${file}`;
    if (await Bun.file(srcPath).exists()) {
      const content = await Bun.file(srcPath).text();
      const outPath = `${distDir}/${file}`;
      const outDir = `${distDir}/${file.split("/").slice(0, -1).join("/")}`;

      if (!(await Bun.file(outDir).exists())) {
        await Bun.$`mkdir -p ${outDir}`.quiet();
      }

      await Bun.write(outPath, content);
      console.log(`✓ Copied ${file}`);
    }
  }
}

async function copyAssets() {
  const assetsDir = `${srcDir}/assets`;
  if (!(await Bun.file(assetsDir).exists())) {
    return;
  }

  const outDir = `${distDir}/assets`;
  await Bun.$`mkdir -p ${outDir}`.quiet();

  const files = await Array.fromAsync(
    new Bun.Glob("**/*").scan({ cwd: assetsDir, onlyFiles: true })
  );

  for (const file of files) {
    const srcPath = `${assetsDir}/${file}`;
    const outPath = `${outDir}/${file}`;
    const content = await Bun.file(srcPath).arrayBuffer();
    await Bun.write(outPath, content);
  }

  console.log(`✓ Copied ${files.length} assets`);
}

async function buildTypeScript() {
  // Find all TypeScript entry points
  const entryPoints: string[] = [];

  const patterns = [
    "background/**/*.{ts,tsx}",
    "popup/**/*.{ts,tsx}",
    "options/**/*.{ts,tsx}",
    "content/**/*.{ts,tsx}",
    "devtools/**/*.{ts,tsx}",
    "offscreen/**/*.{ts,tsx}",
    "page/**/*.{ts,tsx}",
  ];

  for (const pattern of patterns) {
    const glob = new Bun.Glob(pattern);
    const files = await Array.fromAsync(glob.scan({ cwd: srcDir, onlyFiles: true }));
    for (const file of files) {
      // Only include index/main files as entry points
      if (file.includes("index.") || file.includes("panel.") || file.includes("devtools.")) {
        entryPoints.push(`${srcDir}/${file}`);
      }
    }
  }

  if (entryPoints.length === 0) {
    console.log("⚠ No TypeScript entry points found");
    return;
  }

  console.log(`Found ${entryPoints.length} entry points:`);
  for (const entry of entryPoints) {
    console.log(`  - ${entry.replace(srcDir + "/", "")}`);
  }

  // Build with Bun
  const result = await Bun.build({
    entrypoints: entryPoints,
    outdir: distDir,
    format: "esm",
    target: "browser",
    minify: isProd,
    sourcemap: isProd ? "none" : "inline",
    splitting: false,
    external: ["chrome"],
    naming: {
      entry: "[dir]/[name].[ext]",
      chunk: "[name]-[hash].[ext]",
      asset: "[name]-[hash].[ext]",
    },
  });

  if (!result.success) {
    console.error("❌ TypeScript build errors:");
    for (const message of result.logs) {
      console.error(message);
    }
    throw new Error("TypeScript build failed");
  }

  console.log(`✓ Built ${result.outputs.length} JavaScript files`);
}

async function buildCSS() {
  const cssGlob = new Bun.Glob("**/*.css");
  const cssFiles = await Array.fromAsync(cssGlob.scan({ cwd: srcDir, onlyFiles: true }));

  if (cssFiles.length === 0) {
    return;
  }

  for (const file of cssFiles) {
    const srcPath = `${srcDir}/${file}`;
    const outPath = `${distDir}/${file}`;
    const outDir = `${distDir}/${file.split("/").slice(0, -1).join("/")}`;

    if (!(await Bun.file(outDir).exists())) {
      await Bun.$`mkdir -p ${outDir}`.quiet();
    }

    const result = await Bun.build({
      entrypoints: [srcPath],
      minify: isProd,
    });

    if (result.success && result.outputs[0]) {
      await Bun.write(outPath, result.outputs[0]);
    }
  }

  console.log(`✓ Built ${cssFiles.length} CSS files`);
}

// ============================================================================
// Main Build Function
// ============================================================================

async function build() {
  try {
    console.log("\n📦 Starting build...\n");

    await cleanDist();
    await copyManifest();
    await copyHTML();
    await copyAssets();
    await buildCSS();
    await buildTypeScript();

    console.log("\n✅ Build complete!\n");
    console.log(`Output: ${distDir}`);
  } catch (error) {
    console.error("\n❌ Build failed:", error);
    process.exit(1);
  }
}

build();
