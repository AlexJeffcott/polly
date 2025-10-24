#!/usr/bin/env bun

import { existsSync, mkdirSync, rmSync } from "node:fs";
import { join } from "node:path";

// ============================================================================
// Environment & Configuration
// ============================================================================

// Load environment variables from .env file
const envFile = await Bun.file(".env")
  .text()
  .catch(() => "");

const envVars: Record<string, string> = {};
for (const line of envFile.split("\n")) {
  const match = line.match(/^([^#][^=]*?)=(.*)$/);
  if (match?.[1] && match[2]) {
    const key = match[1];
    const value = match[2];
    envVars[key.trim()] = value.trim().replace(/^["']|["']$/g, "");
  }
}

// Load package info
const packageJson = await Bun.file("package.json").json();

// Build configuration
const isProd = process.argv.includes("--prod");
const isWatch = process.argv.includes("--watch");

const env = {
  SUPPORTED_DOMAINS:
    envVars["SUPPORTED_DOMAINS"] || process.env["SUPPORTED_DOMAINS"] || "https://localhost:2222/*",
  EXTENSION_NAME: envVars["EXTENSION_NAME"] || process.env["EXTENSION_NAME"] || "Chrome Extension",
  RELEASE_SPACE_URL: envVars["RELEASE_SPACE_URL"] || process.env["RELEASE_SPACE_URL"] || "",
  FEEDBACK_SPACE_URL: envVars["FEEDBACK_SPACE_URL"] || process.env["FEEDBACK_SPACE_URL"] || "",
  VERSION: packageJson.version,
  BUILD_TIMESTAMP: new Date().toISOString(),
  NODE_ENV: isProd ? "production" : "development",
};

// ============================================================================
// Build Configuration
// ============================================================================

type EntryPoint = {
  in: string;
  out: string;
  type: "ts" | "tsx" | "css" | "html" | "asset";
};

const entryPoints: EntryPoint[] = [
  // Background service worker
  { in: "src/background/index.ts", out: "background/index.js", type: "ts" },

  // Content script
  { in: "src/content/index.ts", out: "content/index.js", type: "ts" },
  {
    in: "src/content/styles.module.css",
    out: "content/styles.css",
    type: "css",
  },

  // Page script (injected into page)
  { in: "src/page/index.ts", out: "page/index.js", type: "ts" },

  // DevTools
  { in: "src/devtools/index.ts", out: "devtools/index.js", type: "ts" },
  { in: "src/devtools/panel.tsx", out: "devtools/panel.js", type: "tsx" },
  {
    in: "src/devtools/panel.module.css",
    out: "devtools/panel.css",
    type: "css",
  },
  {
    in: "src/devtools/devtools.html",
    out: "devtools/devtools.html",
    type: "html",
  },
  { in: "src/devtools/panel.html", out: "devtools/panel.html", type: "html" },

  // Popup
  { in: "src/popup/index.tsx", out: "popup/popup.js", type: "tsx" },
  { in: "src/popup/popup.module.css", out: "popup/popup.css", type: "css" },
  { in: "src/popup/popup.html", out: "popup/popup.html", type: "html" },

  // Options
  { in: "src/options/index.tsx", out: "options/options.js", type: "tsx" },
  {
    in: "src/options/options.module.css",
    out: "options/options.css",
    type: "css",
  },
  { in: "src/options/options.html", out: "options/options.html", type: "html" },

  // Offscreen document
  { in: "src/offscreen/index.ts", out: "offscreen/offscreen.js", type: "ts" },
  {
    in: "src/offscreen/offscreen.html",
    out: "offscreen/offscreen.html",
    type: "html",
  },

  // Assets
  { in: "src/assets/icon16.png", out: "assets/icon16.png", type: "asset" },
  { in: "src/assets/icon48.png", out: "assets/icon48.png", type: "asset" },
  { in: "src/assets/icon128.png", out: "assets/icon128.png", type: "asset" },
];

// ============================================================================
// Manifest Processing
// ============================================================================

// Type definitions for Chrome manifest
type ContentScript = {
  matches: string[];
  [key: string]: unknown;
};

type WebAccessibleResource = {
  matches: string[];
  [key: string]: unknown;
};

type Manifest = {
  name: string;
  version: string;
  host_permissions?: string[];
  content_scripts?: ContentScript[];
  web_accessible_resources?: WebAccessibleResource[];
  [key: string]: unknown;
};

function isManifest(value: unknown): value is Manifest {
  if (typeof value !== "object" || value === null) return false;
  return (
    "name" in value &&
    typeof value.name === "string" &&
    "version" in value &&
    typeof value.version === "string"
  );
}

async function processManifest() {
  try {
    // Read and parse manifest.json
    const manifestFile = Bun.file("src/manifest.json");
    const manifestData = await manifestFile.json();

    if (!isManifest(manifestData)) {
      throw new Error("Invalid manifest.json format");
    }

    const manifest = manifestData;

    // Parse supported domains from comma-separated string
    const domains = env.SUPPORTED_DOMAINS.split(",").map((d) => d.trim());

    // Update manifest with environment variables
    manifest.name = env.EXTENSION_NAME;
    manifest.version = env.VERSION;

    // Replace the template placeholder with actual domains array
    if (manifest.host_permissions) {
      const hostPermissions = manifest.host_permissions.flatMap((permission: string) => {
        if (permission === "${SUPPORTED_DOMAINS}") {
          return domains;
        }
        return permission;
      });
      manifest.host_permissions = hostPermissions;
    }

    // Replace domains in content_scripts matches
    if (manifest.content_scripts) {
      manifest.content_scripts = manifest.content_scripts.map((script) => ({
        ...script,
        matches: script.matches.flatMap((match: string) =>
          match === "${SUPPORTED_DOMAINS}" ? domains : match
        ),
      }));
    }

    // Replace domains in web_accessible_resources matches
    if (manifest.web_accessible_resources) {
      manifest.web_accessible_resources = manifest.web_accessible_resources.map((resource) => ({
        ...resource,
        matches: resource.matches.flatMap((match: string) =>
          match === "${SUPPORTED_DOMAINS}" ? domains : match
        ),
      }));
    }

    // Add Content Security Policy in development
    if (!isProd) {
      manifest["content_security_policy"] = {
        extension_pages: "script-src 'self'; object-src 'self'",
      };
    }

    // Write processed manifest
    await Bun.write("dist/manifest.json", JSON.stringify(manifest, null, 2));
  } catch (error) {
    console.error("✗ Failed to process manifest.json:", error);
    throw error;
  }
}

// ============================================================================
// Build Functions
// ============================================================================

async function cleanDist() {
  try {
    rmSync("dist", { recursive: true, force: true });
  } catch {
    // Directory might not exist, that's fine
  }
  mkdirSync("dist", { recursive: true });
}

async function copyAsset(entry: EntryPoint) {
  try {
    if (!existsSync(entry.in)) {
      console.warn(`⚠️  Asset not found (skipping): ${entry.in}`);
      return;
    }

    const file = Bun.file(entry.in);
    const content = await file.arrayBuffer();
    const outputPath = `dist/${entry.out}`;

    // Ensure output directory exists
    const dir = join("dist", entry.out.split("/").slice(0, -1).join("/"));
    if (dir !== "dist") {
      mkdirSync(dir, { recursive: true });
    }

    await Bun.write(outputPath, content);
  } catch (error) {
    console.warn(`  ✗ Failed to copy ${entry.in}:`, error);
  }
}

async function copyHTML(entry: EntryPoint) {
  try {
    if (!existsSync(entry.in)) {
      console.warn(`⚠️  HTML not found (skipping): ${entry.in}`);
      return;
    }

    const file = Bun.file(entry.in);
    let content = await file.text();

    // Replace template variables in HTML
    content = content
      .replace(/\$\{EXTENSION_NAME\}/g, env.EXTENSION_NAME)
      .replace(/\$\{VERSION\}/g, env.VERSION)
      .replace(/\$\{BUILD_TIMESTAMP\}/g, env.BUILD_TIMESTAMP);

    const outputPath = `dist/${entry.out}`;

    // Ensure output directory exists
    const dir = join("dist", entry.out.split("/").slice(0, -1).join("/"));
    if (dir !== "dist") {
      mkdirSync(dir, { recursive: true });
    }

    await Bun.write(outputPath, content);
  } catch (error) {
    console.warn(`  ✗ Failed to copy ${entry.in}:`, error);
  }
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Build function requires sequential operations
async function buildTypeScript() {
  // Group entries by type
  const tsEntries = entryPoints
    .filter((e) => e.type === "ts" || e.type === "tsx")
    .filter((e) => existsSync(e.in));

  if (tsEntries.length === 0) {
    console.warn("⚠️  No TypeScript files found to build");
    return;
  }

  // Create a map for custom output paths
  const entryMap = new Map(tsEntries.map((e) => [e.in, e.out]));

  const result = await Bun.build({
    entrypoints: tsEntries.map((e) => e.in),
    outdir: "dist",
    format: "esm",
    target: "browser",
    minify: isProd,
    sourcemap: isProd ? "none" : "inline",
    splitting: false, // Chrome extensions don't support module splitting
    external: ["chrome"], // Don't bundle chrome APIs
    define: {
      // Inject environment variables at build time
      "process.env.SUPPORTED_DOMAINS": JSON.stringify(env.SUPPORTED_DOMAINS),
      "process.env.EXTENSION_NAME": JSON.stringify(env.EXTENSION_NAME),
      "process.env.RELEASE_SPACE_URL": JSON.stringify(env.RELEASE_SPACE_URL),
      "process.env.FEEDBACK_SPACE_URL": JSON.stringify(env.FEEDBACK_SPACE_URL),
      "process.env.VERSION": JSON.stringify(env.VERSION),
      "process.env.BUILD_TIMESTAMP": JSON.stringify(env.BUILD_TIMESTAMP),
      "process.env.NODE_ENV": JSON.stringify(env.NODE_ENV),
    },
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

  // Move files to correct output paths
  for (const output of result.outputs) {
    const inputPath = tsEntries.find((e) =>
      output.path.includes(e.in.replace("src/", "").replace(/\.[^.]+$/, ""))
    );
    if (inputPath) {
      const expectedOut = entryMap.get(inputPath.in);
      if (expectedOut && !output.path.endsWith(expectedOut)) {
        try {
          const targetPath = `dist/${expectedOut}`;
          const dir = join("dist", expectedOut.split("/").slice(0, -1).join("/"));
          if (dir !== "dist") {
            mkdirSync(dir, { recursive: true });
          }
          await Bun.write(targetPath, await Bun.file(output.path).arrayBuffer());
        } catch (error) {
          console.error(`  ✗ Failed to move ${output.path}:`, error);
        }
      }
    }
  }
}

async function buildCSS() {
  const cssEntries = entryPoints.filter((e) => e.type === "css").filter((e) => existsSync(e.in));

  if (cssEntries.length === 0) {
    console.warn("⚠️  No CSS files found to build");
    return;
  }

  for (const entry of cssEntries) {
    try {
      const result = await Bun.build({
        entrypoints: [entry.in],
        outdir: "dist",
        minify: isProd,
        naming: entry.out,
      });

      if (!result.success) {
        console.error(`  ✗ Failed to build ${entry.in}:`, result.logs);
        continue;
      }

      // Ensure correct output path
      const targetPath = `dist/${entry.out}`;
      const dir = join("dist", entry.out.split("/").slice(0, -1).join("/"));
      if (dir !== "dist") {
        mkdirSync(dir, { recursive: true });
      }

      // Copy to correct location
      for (const output of result.outputs) {
        await Bun.write(targetPath, await Bun.file(output.path).arrayBuffer());
      }
    } catch (error) {
      console.error(`  ✗ Failed to build ${entry.in}:`, error);
    }
  }
}

async function copyAssets() {
  const assetEntries = entryPoints.filter((e) => e.type === "asset");

  for (const entry of assetEntries) {
    await copyAsset(entry);
  }
}

async function copyHTMLFiles() {
  const htmlEntries = entryPoints.filter((e) => e.type === "html");

  for (const entry of htmlEntries) {
    await copyHTML(entry);
  }
}

// ============================================================================
// Main Build Function
// ============================================================================

async function build() {
  try {
    // Step 1: Clean previous build
    await cleanDist();

    // Step 2: Process manifest with environment variables
    await processManifest();

    // Step 3: Copy HTML files
    await copyHTMLFiles();

    // Step 4: Copy assets (icons, etc.)
    await copyAssets();

    // Step 5: Build CSS files
    await buildCSS();

    // Step 6: Build TypeScript files
    await buildTypeScript();
  } catch (error) {
    console.error("\n❌ Build failed:", error);
    process.exit(1);
  }
}

// ============================================================================
// Watch Mode
// ============================================================================

if (isWatch) {
  // Initial build
  await build();
} else {
  // Single build
  await build();
}
