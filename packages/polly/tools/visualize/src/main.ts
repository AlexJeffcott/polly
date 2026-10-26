// CLI for visualization system

import { randomUUID } from "node:crypto";
import * as fs from "node:fs";
import { constants as osConstants } from "node:os";
import * as path from "node:path";
import { readRecord, readString, readStringArray } from "../../../src/shared/lib/guards";
import { analyzeArchitecture } from "../../analysis/src/extract/architecture";
import { findWorkspacePackageDirs } from "../../analysis/src/extract/project-detector";
import type { ArchitectureAnalysis } from "../../analysis/src/types/architecture";
import { MissingToolPackageError } from "../../tool-deps/src/index.ts";
import { generateStructurizrDSL } from "./codegen/structurizr";
import { type DocumentIdResolver, loadDocumentIdResolver } from "./mesh-document-id";
import {
  collectSnapshotPeerIds,
  loadMeshSnapshot,
  MeshSnapshotError,
  type OverlaySnapshot,
} from "./mesh-snapshot";
import { exportDiagrams } from "./runner/export";

const COLORS = {
  reset: "\x1b[0m",
  red: "\x1b[31m",
  green: "\x1b[32m",
  yellow: "\x1b[33m",
  blue: "\x1b[34m",
  gray: "\x1b[90m",
};

function color(text: string, colorCode: string): string {
  return `${colorCode}${text}${COLORS.reset}`;
}

/** Print a red error to stderr and exit 1. Every failing exit goes through here. */
function fail(message: string): never {
  process.stderr.write(`${color(`\n✗ ${message}\n`, COLORS.red)}\n`);
  process.exit(1);
}

function errorMessage(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

/**
 * Written into a workspace root that has no tsconfig.json of its own, so one
 * program spans every workspace package; removed once analysis finishes.
 */
const WORKSPACE_TSCONFIG = "tsconfig.polly-visualize.json";

/**
 * Top-level key marking a WORKSPACE_TSCONFIG as polly's own: the pid that
 * wrote it and a per-run token, so a run removes only the file it wrote and
 * can tell a stale leftover from a stranger's file.
 */
const WORKSPACE_TSCONFIG_MARKER = "pollyVisualize";

/** Removing the temp tsconfig must also happen when the run is signalled. */
const CLEANUP_SIGNALS = ["SIGINT", "SIGTERM", "SIGHUP"] as const;

type ProjectSetup = {
  tsConfigPath: string;
  projectRoot: string;
  /** Child packages stand in for a missing `workspaces` field. */
  inferWorkspaces: boolean;
  /** Removes the synthesized tsconfig, if one was written. */
  cleanup: () => void;
};

async function main() {
  const args = process.argv.slice(2);
  const command = args[0];

  switch (command) {
    case "--generate":
    case "generate":
      await generateCommand(args.slice(1));
      break;

    case "--export":
    case "export":
      await exportCommand(args.slice(1));
      break;

    case "--serve":
    case "serve":
    case "--view":
    case "view":
      await serveCommand(args.slice(1));
      break;

    case "--help":
    case "help":
      showHelp();
      break;

    default:
      await generateCommand(args);
  }
}

async function generateCommand(args: string[]) {
  console.log(color("\n📊 Analyzing architecture...\n", COLORS.blue));

  let dslPath: string;
  try {
    const { snapshotPath } = parseGenerateArgs(args);
    const snapshot = snapshotPath ? loadAndReportSnapshot(snapshotPath) : undefined;
    // Only the snapshot overlay derives mesh document ids, so only it loads
    // the optional peers that derivation needs; before analysis, to fail fast.
    const resolveDocumentId = snapshot ? await loadResolverOrFail() : undefined;
    const setup = findAndDisplayProjectConfig();
    let analysis: ArchitectureAnalysis;
    try {
      analysis = await analyzeAndDisplayResults(setup);
    } finally {
      setup.cleanup();
    }
    dslPath = generateAndWriteDSL(analysis, snapshot, resolveDocumentId);
  } catch (error) {
    fail(`Architecture analysis failed: ${errorMessage(error)}`);
  }
  displayNextSteps(dslPath);
}

/** Parse the options `polly visualize generate` accepts. */
function parseGenerateArgs(args: string[]): { snapshotPath?: string } {
  const result: { snapshotPath?: string } = {};

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--snapshot") {
      const next = args[i + 1];
      if (!next || next.startsWith("--")) {
        fail("--snapshot requires a file path");
      }
      result.snapshotPath = next;
      i++;
    } else if (arg?.startsWith("--snapshot=")) {
      result.snapshotPath = arg.slice("--snapshot=".length);
    }
  }

  return result;
}

/** Load the document-id resolver; a missing optional peer exits 1 with the install message. */
async function loadResolverOrFail(): Promise<DocumentIdResolver> {
  try {
    return await loadDocumentIdResolver();
  } catch (error) {
    if (error instanceof MissingToolPackageError) fail(error.message);
    throw error;
  }
}

/**
 * polly#127: load a captured `MeshClientPeerStateSnapshot`. A malformed
 * file is a clear error and a non-zero exit with no partial DSL. An
 * empty snapshot (no peers beyond the local node) falls back to the
 * static diagram with a warning.
 */
function loadAndReportSnapshot(snapshotPath: string): OverlaySnapshot | undefined {
  let snapshot: OverlaySnapshot;
  try {
    snapshot = loadMeshSnapshot(snapshotPath);
  } catch (error) {
    const message = error instanceof MeshSnapshotError ? error.message : String(error);
    fail(`Snapshot error: ${message}`);
  }

  const isEmpty =
    snapshot.knownPeerIds.length === 0 &&
    snapshot.presentPeerIds.length === 0 &&
    snapshot.peers.length === 0;
  if (isEmpty) {
    console.log(
      color("⚠ Snapshot has no peers — generating the static diagram only.", COLORS.yellow)
    );
    return undefined;
  }

  const peerCount = collectSnapshotPeerIds(snapshot).length;
  console.log(color(`✓ Loaded runtime snapshot: ${peerCount} peer(s)`, COLORS.green));
  return snapshot;
}

/**
 * Resolve what to analyse, in order: ./tsconfig.json; a workspace root (a
 * package.json whose `workspaces`, or failing that whose child directories,
 * name packages), analysed as one program; ../tsconfig.json.
 */
function findAndDisplayProjectConfig(): ProjectSetup {
  const cwd = process.cwd();
  const ownTsConfig = path.join(cwd, "tsconfig.json");
  const parentTsConfig = path.join(cwd, "..", "tsconfig.json");

  if (fs.existsSync(ownTsConfig)) return setupFromTsConfig(ownTsConfig);

  const workspace = findWorkspacePackageDirs(cwd);
  if (workspace.dirs.length > 0) return setupWorkspaceRoot(cwd, workspace);

  if (fs.existsSync(parentTsConfig)) return setupFromTsConfig(parentTsConfig);

  fail(
    [
      "No TypeScript project found. Searched for:",
      `    ${ownTsConfig}`,
      `    ${path.join(cwd, "package.json")} with workspace packages`,
      `    ${parentTsConfig}`,
      "  Run polly visualize from a directory that has a tsconfig.json, or from a",
      "  workspace root (a package.json with package subdirectories or `workspaces`).",
    ].join("\n")
  );
}

function setupFromTsConfig(tsConfigPath: string): ProjectSetup {
  console.log(color(`   Using: ${tsConfigPath}`, COLORS.gray));

  const projectRoot = findProjectRoot();
  if (!projectRoot) {
    const cwd = process.cwd();
    fail(
      `No project root found: none of manifest.json, package.json or tsconfig.json in ${cwd} or ${path.join(cwd, "..")}`
    );
  }
  console.log(color(`   Project: ${projectRoot}`, COLORS.gray));

  displayProjectType(projectRoot);

  return { tsConfigPath, projectRoot, inferWorkspaces: false, cleanup: () => undefined };
}

function setupWorkspaceRoot(
  root: string,
  workspace: { dirs: string[]; declared: boolean }
): ProjectSetup {
  const tsConfigPath = path.join(root, WORKSPACE_TSCONFIG);
  if (fs.existsSync(tsConfigPath)) refuseOrReplaceStale(tsConfigPath);

  const token = randomUUID();
  const removeOwn = () => {
    if (readMarker(tsConfigPath)?.token === token) fs.rmSync(tsConfigPath, { force: true });
  };

  // A signal kills the process before any `finally` runs, so remove the file
  // here too, then exit as the default action would (128 + signal number).
  // Registered before the write: a signal that lands once the file exists but
  // before its handler does would otherwise take the default action and leave
  // the file behind.
  const handlers = CLEANUP_SIGNALS.map((signal) => {
    const handler = () => {
      removeOwn();
      process.exit(128 + osConstants.signals[signal]);
    };
    process.on(signal, handler);
    return { signal, handler };
  });
  try {
    fs.writeFileSync(tsConfigPath, workspaceTsConfig(root, workspace.dirs, token), "utf-8");
  } catch (error) {
    for (const { signal, handler } of handlers) process.off(signal, handler);
    throw error;
  }

  const names = workspace.dirs.map((dir) => path.relative(root, dir)).join(", ");
  console.log(color(`   Using: workspace packages ${names}`, COLORS.gray));
  console.log(color(`   Project: ${root}`, COLORS.gray));
  displayProjectType(root);

  return {
    tsConfigPath,
    projectRoot: root,
    inferWorkspaces: !workspace.declared,
    cleanup: () => {
      for (const { signal, handler } of handlers) process.off(signal, handler);
      removeOwn();
    },
  };
}

/** The marker of a polly-written temp tsconfig, or undefined for any other file. */
function readMarker(filePath: string): { pid: number; token: string } | undefined {
  const marker = readRecord(readJsonRecord(filePath)?.[WORKSPACE_TSCONFIG_MARKER]);
  const pid = marker?.["pid"];
  const token = readString(marker?.["token"]);
  return typeof pid === "number" && token ? { pid, token } : undefined;
}

function isRunning(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    // EPERM: the process exists but belongs to another user.
    return error instanceof Error && "code" in error && error.code === "EPERM";
  }
}

/**
 * A temp tsconfig left by a run that died is replaced. One a live run is
 * using, or one polly did not write, is left alone and the run stops.
 */
function refuseOrReplaceStale(tsConfigPath: string): void {
  const marker = readMarker(tsConfigPath);
  if (!marker) {
    fail(
      `${tsConfigPath} exists and was not written by polly visualize; rename or delete it so generate can write its own`
    );
  }
  if (marker.pid !== process.pid && isRunning(marker.pid)) {
    fail(
      `${tsConfigPath} is in use by another polly visualize run (pid ${marker.pid}). Wait for it to finish; if no such run is active, the file is safe to delete.`
    );
  }
  console.log(color(`   Replacing stale ${tsConfigPath} left by an earlier run`, COLORS.yellow));
  fs.rmSync(tsConfigPath, { force: true });
}

/**
 * One tsconfig spanning every workspace package: each package's own
 * `include` (default all files) re-rooted at the workspace root, and the
 * first JSX settings any package declares.
 */
function workspaceTsConfig(root: string, dirs: string[], token: string): string {
  const include: string[] = [];
  const jsx: Record<string, string> = {};

  for (const dir of dirs) {
    const rel = path.relative(root, dir).split(path.sep).join("/");
    const own = readJsonRecord(path.join(dir, "tsconfig.json"));
    const patterns = readStringArray(own?.["include"]) ?? ["**/*"];
    include.push(...patterns.map((pattern) => path.posix.join(rel, pattern)));

    const options = readRecord(own?.["compilerOptions"]);
    for (const key of ["jsx", "jsxImportSource"]) {
      const value = readString(options?.[key]);
      if (value && jsx[key] === undefined) jsx[key] = value;
    }
  }

  const config = {
    [WORKSPACE_TSCONFIG_MARKER]: {
      note: "Temporary file written by polly visualize generate; safe to delete.",
      pid: process.pid,
      token,
    },
    compilerOptions: {
      target: "ESNext",
      module: "ESNext",
      moduleResolution: "bundler",
      strict: true,
      skipLibCheck: true,
      noEmit: true,
      ...jsx,
    },
    include,
    exclude: ["**/node_modules", "**/dist"],
  };
  return `${JSON.stringify(config, null, 2)}\n`;
}

/** A JSON file's top-level object, or undefined when absent or not plain JSON. */
function readJsonRecord(filePath: string): Record<string, unknown> | undefined {
  if (!fs.existsSync(filePath)) return undefined;
  try {
    return readRecord(JSON.parse(fs.readFileSync(filePath, "utf-8")));
  } catch {
    return undefined;
  }
}

function displayProjectType(projectRoot: string): void {
  const hasManifest = fs.existsSync(path.join(projectRoot, "manifest.json"));
  const projectType = hasManifest ? "Chrome Extension" : "Detecting from project structure...";
  console.log(color(`   Type: ${projectType}`, COLORS.gray));
}

async function analyzeAndDisplayResults(setup: ProjectSetup): Promise<ArchitectureAnalysis> {
  const { tsConfigPath, projectRoot, inferWorkspaces } = setup;
  const analysis = await analyzeArchitecture({ tsConfigPath, projectRoot, inferWorkspaces });

  console.log(color(`\n✓ Found ${Object.keys(analysis.contexts).length} context(s)`, COLORS.green));
  console.log(color(`✓ Found ${analysis.messageFlows.length} message flow(s)`, COLORS.green));
  console.log(color(`✓ Found ${analysis.integrations.length} integration(s)`, COLORS.green));

  displayArchitectureSummary(analysis);

  return analysis;
}

function displayArchitectureSummary(analysis: ArchitectureAnalysis): void {
  console.log(color("\n📋 Architecture Summary:\n", COLORS.blue));

  console.log(color("  Contexts:", COLORS.blue));
  for (const [contextType, contextInfo] of Object.entries(analysis.contexts)) {
    console.log(color(`    • ${contextType}`, COLORS.gray));
    console.log(color(`      - ${contextInfo.handlers.length} handler(s)`, COLORS.gray));
    console.log(color(`      - ${contextInfo.chromeAPIs.length} Chrome API(s)`, COLORS.gray));
    if (contextInfo.components) {
      console.log(color(`      - ${contextInfo.components.length} component(s)`, COLORS.gray));
    }
  }

  if (analysis.integrations.length > 0) {
    console.log(color("\n  External Integrations:", COLORS.blue));
    for (const integration of analysis.integrations) {
      console.log(color(`    • ${integration.name} (${integration.type})`, COLORS.gray));
    }
  }
}

function generateAndWriteDSL(
  analysis: ArchitectureAnalysis,
  snapshot?: OverlaySnapshot,
  resolveDocumentId?: DocumentIdResolver
): string {
  console.log(color("\n📝 Generating Structurizr DSL...\n", COLORS.blue));

  const contextTypes = Object.keys(analysis.contexts);
  const dsl = generateStructurizrDSL(analysis, {
    includeDynamicDiagrams: true,
    includeComponentDiagrams: true,
    componentDiagramContexts: contextTypes.length > 0 ? contextTypes : ["background"],
    snapshot,
    resolveDocumentId,
  });

  const outputDir = path.join(process.cwd(), "docs");
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  const dslPath = path.join(outputDir, "architecture.dsl");
  fs.writeFileSync(dslPath, dsl, "utf-8");

  return dslPath;
}

function displayNextSteps(dslPath: string): void {
  const outputDir = path.join(process.cwd(), "docs");

  console.log(color("✅ Architecture documentation generated!\n", COLORS.green));
  console.log(`   File: ${color(dslPath, COLORS.blue)}`);
  console.log();
  console.log(color("📝 Next steps:", COLORS.blue));
  console.log();
  console.log("   1. Export diagrams:");
  console.log("      polly visualize --export");
  console.log();
  console.log("   2. View in browser:");
  console.log("      polly visualize --serve");
  console.log();
  console.log(color("💡 Alternative: Structurizr Lite", COLORS.gray));
  console.log(color("   docker run -it --rm -p 8080:8080 \\", COLORS.gray));
  console.log(color(`     -v ${outputDir}:/usr/local/structurizr \\`, COLORS.gray));
  console.log(color("     structurizr/lite", COLORS.gray));
  console.log();
  console.log(color("💡 Upload to Structurizr Cloud:", COLORS.gray));
  console.log(color("   1. Sign up at https://structurizr.com", COLORS.gray));
  console.log(color("   2. Create a workspace and get API credentials", COLORS.gray));
  console.log(
    color("   3. docker run -it --rm -v $(pwd)/docs:/usr/local/structurizr \\", COLORS.gray)
  );
  console.log(
    color("        structurizr/cli push -id WORKSPACE_ID -key KEY -secret SECRET \\", COLORS.gray)
  );
  console.log(color("        -workspace /usr/local/structurizr/architecture.dsl", COLORS.gray));
  console.log();
}

async function exportCommand(_args: string[]) {
  console.log(color("\n📤 Generating static site...\n", COLORS.blue));

  // Find DSL file
  const dslPath = path.join(process.cwd(), "docs", "architecture.dsl");
  if (!fs.existsSync(dslPath)) {
    fail(`No DSL found at ${dslPath}. Run polly visualize --generate first.`);
  }

  try {
    const outputDir = path.join(process.cwd(), "docs", "site");

    console.log(color(`   DSL: ${dslPath}`, COLORS.gray));
    console.log(color(`   Output: ${outputDir}`, COLORS.gray));
    console.log();

    // Export static site
    const result = await exportDiagrams({
      dslPath,
      outputDir,
      onProgress: (message) => {
        console.log(color(`   ${message}`, COLORS.gray));
      },
    });

    if (!result.success) {
      fail(`Export failed: ${result.error ?? "no reason given"}`);
    }

    // Show results
    console.log(color("\n✅ Static site generated!\n", COLORS.green));
    console.log(color("📁 Location:", COLORS.blue));
    console.log(`   ${outputDir}`);
    console.log();
    console.log(color("💡 Next steps:", COLORS.gray));
    console.log(color("   • View: polly visualize --serve", COLORS.gray));
    console.log(color("   • Or open: docs/site/index.html", COLORS.gray));
    console.log();
  } catch (error) {
    fail(`Export failed: ${errorMessage(error)}`);
  }
}

async function serveCommand(args: string[]) {
  console.log(color("\n🌐 Starting static site server...\n", COLORS.blue));

  const siteDir = path.join(process.cwd(), "docs", "site");
  const indexPath = path.join(siteDir, "index.html");
  if (!fs.existsSync(indexPath)) {
    fail(`No static site found at ${indexPath}. Run polly visualize --export first.`);
  }

  try {
    // Parse port argument
    const portArg = args.find((arg) => arg.startsWith("--port="));
    const port = portArg ? Number.parseInt(portArg.replace("--port=", ""), 10) : 3000;

    console.log(color(`   Site: ${siteDir}`, COLORS.gray));
    console.log(color(`   Port: ${port}`, COLORS.gray));
    console.log();

    // Start Bun's static file server
    const BunGlobal = globalThis.Bun;
    if (!BunGlobal) {
      throw new Error("Bun runtime is required to run the server");
    }

    void BunGlobal.serve({
      port,
      fetch(req: Request) {
        const url = new URL(req.url);
        const filePath = path.join(siteDir, url.pathname === "/" ? "index.html" : url.pathname);

        if (fs.existsSync(filePath) && fs.statSync(filePath).isFile()) {
          const file = BunGlobal.file(filePath);
          return new Response(file);
        }

        return new Response("Not found", { status: 404 });
      },
    });

    console.log(color("\n✅ Server started!\n", COLORS.green));
    console.log(`   ${color(`http://localhost:${port}`, COLORS.blue)}`);
    console.log();
    console.log(color("Press Ctrl+C to stop the server", COLORS.gray));
    console.log();

    // Auto-open browser
    if (process.platform === "darwin") {
      await BunGlobal.spawn(["open", `http://localhost:${port}`]);
    } else if (process.platform === "linux") {
      await BunGlobal.spawn(["xdg-open", `http://localhost:${port}`]);
    } else if (process.platform === "win32") {
      await BunGlobal.spawn(["cmd", "/c", "start", `http://localhost:${port}`]);
    }

    // Keep process alive indefinitely
    await new Promise(() => {
      // Intentionally empty - keeps the server running
    });
  } catch (error) {
    fail(`Serve failed: ${errorMessage(error)}`);
  }
}

function showHelp() {
  console.log(`
${color("polly visualize", COLORS.blue)} - Architecture visualization tool

Hand-drawn architecture diagrams rot the moment the code moves. This reads the
real handlers, message flows and execution contexts straight from source, so the
picture always matches what actually ships.

${color("Supports:", COLORS.blue)}

  • Chrome Extensions (manifest.json)
  • PWAs (public/manifest.json)
  • WebSocket/Server Apps (ws, socket.io, elysia)
  • Electron Apps
  • Generic TypeScript Projects

${color("Commands:", COLORS.blue)}

  ${color("polly visualize", COLORS.green)}
  ${color("polly visualize --generate", COLORS.green)}
    Analyze codebase and generate Structurizr DSL

  ${color("polly visualize generate --snapshot <path>", COLORS.green)}
    Overlay a captured MeshClientPeerStateSnapshot — runtime mesh peers
    and sync-state-coloured replication edges — onto the diagram

  ${color("polly visualize --export", COLORS.green)}
    Generate static HTML site with interactive diagrams (requires Docker)

  ${color("polly visualize --serve", COLORS.green)}
  ${color("polly visualize --serve --port=3000", COLORS.green)}
    Serve the static site in browser

  ${color("polly visualize --help", COLORS.green)}
    Show this help message

${color("Getting Started:", COLORS.blue)}

  1. Run ${color("polly visualize", COLORS.green)} from your project root
  2. Find generated ${color("docs/architecture.dsl", COLORS.blue)}
  3. View with Structurizr Lite (see instructions after generation)

${color("What gets generated:", COLORS.blue)}

  • System Context diagram - Your app + external systems
  • Container diagram - App contexts (background, content, server, client, etc.)
  • Component diagrams - Internal components within contexts
  • Dynamic diagrams - Message flows between contexts

${color("Learn More:", COLORS.blue)}

  Documentation: https://github.com/fairfox/web-ext
  Structurizr: https://structurizr.com
  C4 Model: https://c4model.com
`);
}

function findProjectRoot(): string | null {
  const locations = [process.cwd(), path.join(process.cwd(), "..")];

  for (const loc of locations) {
    // Check for any project marker file
    if (
      fs.existsSync(path.join(loc, "manifest.json")) ||
      fs.existsSync(path.join(loc, "package.json")) ||
      fs.existsSync(path.join(loc, "tsconfig.json"))
    ) {
      return loc;
    }
  }

  return null;
}

main().catch((error) => {
  fail(`polly visualize failed: ${errorMessage(error)}`);
});
