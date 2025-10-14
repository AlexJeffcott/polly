#!/usr/bin/env bun
/**
 * Extension Build Script
 *
 * Called by the web-ext CLI to build user extensions.
 * Reads configuration from environment variables set by CLI.
 */

// Configuration from CLI via environment
const srcDir = process.env["WEB_EXT_SRC"] || "src";
const distDir = process.env["WEB_EXT_DIST"] || "dist";
const manifestPath = process.env["WEB_EXT_MANIFEST"] || "manifest.json";
const isProd = process.env["WEB_EXT_PROD"] === "true";

// ============================================================================
// Build Functions
// ============================================================================

async function cleanDist() {
  // Use Bun shell for directory operations
  await Bun.$`rm -rf ${distDir}`.quiet();
  await Bun.$`mkdir -p ${distDir}`.quiet();
}

async function copyManifest() {
  if (!(await Bun.file(manifestPath).exists())) {
    throw new Error(`manifest.json not found at: ${manifestPath}`);
  }

  const manifest = await Bun.file(manifestPath).json();
  await Bun.write(`${distDir}/manifest.json`, JSON.stringify(manifest, null, 2));
}

async function copyHTML() {
  const htmlGlob = new Bun.Glob("**/*.html");
  const htmlFiles = await Array.fromAsync(htmlGlob.scan({ cwd: srcDir, onlyFiles: true }));

  for (const file of htmlFiles) {
    const srcPath = `${srcDir}/${file}`;
    const outPath = `${distDir}/${file}`;
    const outDir = `${distDir}/${file.split("/").slice(0, -1).join("/")}`;

    if (!(await Bun.file(outDir).exists())) {
      await Bun.$`mkdir -p ${outDir}`.quiet();
    }

    const content = await Bun.file(srcPath).text();
    await Bun.write(outPath, content);
  }
}

async function copyAssets() {
  const assetsDir = `${srcDir}/assets`;
  if (!(await Bun.file(assetsDir).exists())) {
    return;
  }

  const outDir = `${distDir}/assets`;
  await Bun.$`mkdir -p ${outDir}`.quiet();

  const glob = new Bun.Glob("**/*");
  const files = await Array.fromAsync(glob.scan({ cwd: assetsDir, onlyFiles: true }));

  for (const file of files) {
    const srcPath = `${assetsDir}/${file}`;
    const outPath = `${outDir}/${file}`;
    const fileOutDir = `${outDir}/${file.split("/").slice(0, -1).join("/")}`;

    if (!(await Bun.file(fileOutDir).exists())) {
      await Bun.$`mkdir -p ${fileOutDir}`.quiet();
    }

    const content = await Bun.file(srcPath).arrayBuffer();
    await Bun.write(outPath, content);
  }
}

async function buildTypeScript() {
  // Find TypeScript/TSX entry points
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
      // Only main entry files (index, panel, devtools, etc.)
      if (
        file.includes("index.") ||
        file.includes("panel.") ||
        file.includes("devtools.") ||
        file.endsWith("worker.ts")
      ) {
        entryPoints.push(`${srcDir}/${file}`);
      }
    }
  }

  if (entryPoints.length === 0) {
    return;
  }

  // Build with Bun
  const result = await Bun.build({
    entrypoints: entryPoints,
    outdir: distDir,
    format: "esm",
    target: "browser",
    minify: isProd,
    sourcemap: isProd ? "none" : "inline",
    splitting: false, // Chrome extensions don't support module splitting
    external: ["chrome"], // Don't bundle chrome APIs
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
}

// ============================================================================
// Main Build
// ============================================================================

async function build() {
  try {
    await cleanDist();
    await copyManifest();
    await copyHTML();
    await copyAssets();
    await buildCSS();
    await buildTypeScript();
  } catch (error) {
    console.error("\n❌ Build failed:", error);
    process.exit(1);
  }
}

build();
