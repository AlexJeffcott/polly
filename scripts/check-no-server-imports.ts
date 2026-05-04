#!/usr/bin/env bun

/**
 * BROWSER-CONTEXT IMPORT ENFORCEMENT
 *
 * Polly has files that target browser execution contexts (Chrome extension
 * surfaces, popup UI, content scripts). Importing `node:fs`, `bun:sqlite`,
 * `node:child_process`, etc. into those files crashes at runtime because
 * the corresponding host APIs don't exist.
 *
 * The directories below are browser-only by construction. Any
 * server/runtime-host module reaching them is a bug.
 *
 *   src/popup/**         — extension popup UI
 *   src/content/**       — content scripts injected into web pages
 *   src/devtools/**      — devtools panel
 *   src/options/**       — extension options page
 *   src/offscreen/**     — offscreen document
 *   src/page/**          — in-page injected scripts
 *   src/ui/**            — shared UI atoms / molecules / pages
 *   src/polly-ui/**      — published UI components
 *   tools/test/src/browser/** — browser test runtime
 */

import { readdir } from "node:fs/promises";
import { join, relative } from "node:path";

interface Violation {
  file: string;
  line: number;
  content: string;
}

const violations: Violation[] = [];
const rootDir = process.cwd();

const bannedModules = [
  // Bun server-only APIs
  "bun:sqlite",
  "bun:ffi",
  "bun:jsc",
  // Node.js server-only modules
  "node:fs",
  "node:fs/promises",
  "node:path",
  "node:child_process",
  "node:net",
  "node:os",
  "node:http",
  "node:https",
  "node:stream",
  "node:worker_threads",
  "node:cluster",
  "node:tls",
  "node:dns",
  // Server-only npm packages
  "better-sqlite3",
  "sqlite3",
  "ws",
];

const browserDirs = [
  "src/popup",
  "src/content",
  "src/devtools",
  "src/options",
  "src/offscreen",
  "src/page",
  "src/ui",
  "src/polly-ui",
  "tools/test/src/browser",
];

const escaped = bannedModules.map((m) => m.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|");
const bannedPattern = new RegExp(
  `(?:import|export)\\s+.*?from\\s+['"](?:${escaped})(?:/[^'"]*)?['"]|require\\(\\s*['"](?:${escaped})(?:/[^'"]*)?['"]\\s*\\)`
);

async function scanDirectory(dir: string): Promise<void> {
  let entries: import("node:fs").Dirent[];
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (entry.name === "node_modules" || entry.name === "dist" || entry.name === ".cache") {
        continue;
      }
      await scanDirectory(fullPath);
    } else if (entry.isFile() && (entry.name.endsWith(".ts") || entry.name.endsWith(".tsx"))) {
      // Skip test files — they may legitimately mock node modules.
      const rel = relative(rootDir, fullPath);
      if (rel.includes("__tests__") || rel.includes(".test.") || rel.includes(".spec.")) {
        continue;
      }
      // tools/test/src/browser/run.ts is the node-side orchestrator that
      // boots the browser bundle — it intentionally uses node APIs.
      if (rel === "tools/test/src/browser/run.ts") {
        continue;
      }
      await scanFile(fullPath);
    }
  }
}

async function scanFile(filePath: string): Promise<void> {
  const content = await Bun.file(filePath).text();
  const lines = content.split("\n");

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (!line) {
      continue;
    }

    const trimmed = line.trim();
    if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*")) {
      continue;
    }

    if (bannedPattern.test(line)) {
      violations.push({
        file: relative(rootDir, filePath),
        line: i + 1,
        content: trimmed,
      });
    }
  }
}

for (const dir of browserDirs) {
  await scanDirectory(join(rootDir, dir));
}

if (violations.length === 0) {
  process.stdout.write("✅ No server-only imports in browser code\n");
  process.exit(0);
}

process.stderr.write(`❌ ${violations.length} server import(s) in browser code:\n\n`);
for (const v of violations) {
  process.stderr.write(`  ${v.file}:${v.line}\n    ${v.content}\n\n`);
}
process.exit(1);
