#!/usr/bin/env bun
// CLI for visualization system

import * as fs from "node:fs";
import * as path from "node:path";
import { analyzeArchitecture } from "../../analysis/src/extract/architecture.ts";
import { generateStructurizrDSL } from "./codegen/structurizr";
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

async function main() {
  const args = process.argv.slice(2);
  const command = args[0];

  switch (command) {
    case "--generate":
    case "generate":
      await generateCommand();
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
      await generateCommand();
  }
}

async function generateCommand() {
  console.log(color("\n📊 Analyzing architecture...\n", COLORS.blue));

  try {
    // Find tsconfig
    const tsConfigPath = findTsConfig();
    if (!tsConfigPath) {
      console.error(color("❌ Could not find tsconfig.json", COLORS.red));
      console.error("   Run this command from your project root");
      process.exit(1);
    }

    console.log(color(`   Using: ${tsConfigPath}`, COLORS.gray));

    // Find project root
    const projectRoot = findProjectRoot();
    if (!projectRoot) {
      console.error(color("❌ Could not find project root", COLORS.red));
      console.error("   Run this command from a directory with manifest.json, package.json, or tsconfig.json");
      process.exit(1);
    }

    console.log(color(`   Project: ${projectRoot}`, COLORS.gray));

    // Detect and display project type
    const hasManifest = fs.existsSync(path.join(projectRoot, "manifest.json"));
    if (hasManifest) {
      console.log(color(`   Type: Chrome Extension`, COLORS.gray));
    } else {
      console.log(color(`   Type: Detecting from project structure...`, COLORS.gray));
    }

    // Analyze architecture
    const analysis = await analyzeArchitecture({
      tsConfigPath,
      projectRoot,
    });

    console.log(
      color(`\n✓ Found ${Object.keys(analysis.contexts).length} context(s)`, COLORS.green)
    );
    console.log(color(`✓ Found ${analysis.messageFlows.length} message flow(s)`, COLORS.green));
    console.log(color(`✓ Found ${analysis.integrations.length} integration(s)`, COLORS.green));

    // Show summary
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

    // Generate Structurizr DSL
    console.log(color("\n📝 Generating Structurizr DSL...\n", COLORS.blue));

    const dsl = generateStructurizrDSL(analysis, {
      includeDynamicDiagrams: true,
      includeComponentDiagrams: true,
      componentDiagramContexts: ["background"],
    });

    // Write to file
    const outputDir = path.join(process.cwd(), "docs");
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true });
    }

    const dslPath = path.join(outputDir, "architecture.dsl");
    fs.writeFileSync(dslPath, dsl, "utf-8");

    console.log(color("✅ Architecture documentation generated!\n", COLORS.green));
    console.log(`   File: ${color(dslPath, COLORS.blue)}`);
    console.log();
    console.log(color("📝 Next steps:", COLORS.blue));
    console.log();
    console.log("   1. Export diagrams:");
    console.log("      bun visualize --export");
    console.log();
    console.log("   2. View in browser:");
    console.log("      bun visualize --serve");
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
  } catch (error) {
    console.error(color("\n❌ Generation failed:", COLORS.red));
    console.error(`   ${error instanceof Error ? error.message : String(error)}`);
    if (error instanceof Error && error.stack) {
      console.error(color("\nStack trace:", COLORS.gray));
      console.error(color(error.stack, COLORS.gray));
    }
    process.exit(1);
  }
}

async function exportCommand(args: string[]) {
  console.log(color("\n📤 Generating static site...\n", COLORS.blue));

  try {
    // Find DSL file
    const dslPath = path.join(process.cwd(), "docs", "architecture.dsl");
    if (!fs.existsSync(dslPath)) {
      console.error(color("❌ DSL file not found", COLORS.red));
      console.error("   Expected: docs/architecture.dsl");
      console.error("   Run 'bun visualize' first to generate the DSL");
      process.exit(1);
    }

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
      console.error(color("\n❌ Export failed:", COLORS.red));
      console.error(`   ${result.error}`);
      process.exit(1);
    }

    // Show results
    console.log(color("\n✅ Static site generated!\n", COLORS.green));
    console.log(color("📁 Location:", COLORS.blue));
    console.log(`   ${outputDir}`);
    console.log();
    console.log(color("💡 Next steps:", COLORS.gray));
    console.log(color("   • View: bun visualize --serve", COLORS.gray));
    console.log(color("   • Or open: docs/site/index.html", COLORS.gray));
    console.log();
  } catch (error) {
    console.error(color("\n❌ Export failed:", COLORS.red));
    console.error(`   ${error instanceof Error ? error.message : String(error)}`);
    if (error instanceof Error && error.stack) {
      console.error(color("\nStack trace:", COLORS.gray));
      console.error(color(error.stack, COLORS.gray));
    }
    process.exit(1);
  }
}

async function serveCommand(args: string[]) {
  console.log(color("\n🌐 Starting static site server...\n", COLORS.blue));

  try {
    const siteDir = path.join(process.cwd(), "docs", "site");
    const indexPath = path.join(siteDir, "index.html");

    if (!fs.existsSync(indexPath)) {
      console.error(color("❌ Static site not found", COLORS.red));
      console.error("   Expected: docs/site/index.html");
      console.error("   Run 'bun visualize --export' first to generate the site");
      process.exit(1);
    }

    // Parse port argument
    const portArg = args.find((arg) => arg.startsWith("--port="));
    const port = portArg ? parseInt(portArg.replace("--port=", "")) : 3000;

    console.log(color(`   Site: ${siteDir}`, COLORS.gray));
    console.log(color(`   Port: ${port}`, COLORS.gray));
    console.log();

    // Start Bun's static file server
    const BunGlobal = (globalThis as any).Bun;
    if (!BunGlobal) {
      throw new Error("Bun runtime is required to run the server");
    }

    const server = BunGlobal.serve({
      port,
      fetch(req: Request) {
        const url = new URL(req.url);
        let filePath = path.join(siteDir, url.pathname === "/" ? "index.html" : url.pathname);

        if (fs.existsSync(filePath) && fs.statSync(filePath).isFile()) {
          const file = BunGlobal.file(filePath);
          return new Response(file);
        }

        return new Response("Not found", { status: 404 });
      },
    });

    console.log(color(`\n✅ Server started!\n`, COLORS.green));
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

    // Keep process alive
    await new Promise(() => {});
  } catch (error) {
    console.error(color("\n❌ Failed to start server:", COLORS.red));
    console.error(`   ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}

function showHelp() {
  console.log(`
${color("bun visualize", COLORS.blue)} - Architecture visualization tool

${color("Supports:", COLORS.blue)}

  • Chrome Extensions (manifest.json)
  • PWAs (public/manifest.json)
  • WebSocket/Server Apps (ws, socket.io, elysia)
  • Electron Apps
  • Generic TypeScript Projects

${color("Commands:", COLORS.blue)}

  ${color("bun visualize", COLORS.green)}
  ${color("bun visualize --generate", COLORS.green)}
    Analyze codebase and generate Structurizr DSL

  ${color("bun visualize --export", COLORS.green)}
    Generate static HTML site with interactive diagrams (requires Docker)

  ${color("bun visualize --serve", COLORS.green)}
  ${color("bun visualize --serve --port=3000", COLORS.green)}
    Serve the static site in browser

  ${color("bun visualize --help", COLORS.green)}
    Show this help message

${color("Getting Started:", COLORS.blue)}

  1. Run ${color("bun visualize", COLORS.green)} from your project root
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

function findTsConfig(): string | null {
  const locations = [
    path.join(process.cwd(), "tsconfig.json"),
    path.join(process.cwd(), "..", "tsconfig.json"),
  ];

  for (const loc of locations) {
    if (fs.existsSync(loc)) {
      return loc;
    }
  }

  return null;
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
  console.error(color("\n❌ Fatal error:", COLORS.red));
  console.error(`   ${error instanceof Error ? error.message : String(error)}`);
  if (error instanceof Error && error.stack) {
    console.error(color("\nStack trace:", COLORS.gray));
    console.error(color(error.stack, COLORS.gray));
  }
  process.exit(1);
});
