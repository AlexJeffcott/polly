// Project type detection and configuration
// Detects project type and infers entry points from tsconfig.json, package.json, etc.

import * as fs from "node:fs";
import * as path from "node:path";
import type { ProjectConfig } from "../types/architecture";

/**
 * Detect project type and generate configuration
 * Falls back to tsconfig.json when manifest.json is not available
 */
export class ProjectDetector {
  private projectRoot: string;

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
  }

  /**
   * Detect project type and return configuration
   */
  detect(): ProjectConfig {
    // Check for Chrome extension manifest
    const manifestPath = path.join(this.projectRoot, "manifest.json");
    if (fs.existsSync(manifestPath)) {
      return this.detectChromeExtension(manifestPath);
    }

    // Check for PWA manifest
    const pwaManifestPath = path.join(this.projectRoot, "public", "manifest.json");
    if (fs.existsSync(pwaManifestPath)) {
      return this.detectPWA(pwaManifestPath);
    }

    // Check for Electron
    const packageJsonPath = path.join(this.projectRoot, "package.json");
    if (fs.existsSync(packageJsonPath)) {
      const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, "utf-8"));

      if (packageJson.dependencies?.electron || packageJson.devDependencies?.electron) {
        return this.detectElectron(packageJson);
      }

      // Check for WebSocket/server patterns in dependencies
      const deps = {
        ...packageJson.dependencies,
        ...packageJson.devDependencies,
      };

      if (
        deps?.ws ||
        deps?.["socket.io"] ||
        deps?.elysia ||
        deps?.express ||
        deps?.fastify ||
        deps?.hono ||
        deps?.koa
      ) {
        return this.detectWebSocketApp(packageJson);
      }

      // Also check with content analysis even without explicit dependencies
      // (Bun has built-in WebSocket support, no dependencies needed)
      const serverResult = this.detectWebSocketApp(packageJson);
      if (Object.keys(serverResult.entryPoints).length > 0) {
        return serverResult;
      }
    } else {
      // No package.json - try WebSocket/server detection anyway
      const serverResult = this.detectWebSocketApp({});
      if (Object.keys(serverResult.entryPoints).length > 0) {
        return serverResult;
      }
    }

    // Fallback: Generic TypeScript project
    return this.detectGenericProject();
  }

  /**
   * Detect Chrome extension from manifest.json
   */
  private detectChromeExtension(manifestPath: string): ProjectConfig {
    const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    const entryPoints: Record<string, string> = {};

    this.detectBackgroundEntry(manifest, entryPoints);
    this.detectContentScriptEntry(manifest, entryPoints);
    this.detectPopupEntry(manifest, entryPoints);
    this.detectOptionsEntry(manifest, entryPoints);

    return {
      type: "chrome-extension",
      entryPoints,
      metadata: {
        name: manifest.name,
        version: manifest.version,
        description: manifest.description,
      },
    };
  }

  /**
   * Detect background script entry point
   */
  private detectBackgroundEntry(
    manifest: Record<string, unknown>,
    entryPoints: Record<string, string>
  ): void {
    const background = manifest.background;
    if (!background) return;

    const file = background.service_worker || background.scripts?.[0] || background.page;
    if (file) {
      entryPoints["background"] = this.findSourceFile(file);
    }
  }

  /**
   * Detect content script entry point
   */
  private detectContentScriptEntry(
    manifest: Record<string, unknown>,
    entryPoints: Record<string, string>
  ): void {
    const contentScripts = manifest.content_scripts;
    if (!contentScripts || contentScripts.length === 0) return;

    const firstScript = contentScripts[0].js?.[0];
    if (firstScript) {
      entryPoints["content"] = this.findSourceFile(firstScript);
    }
  }

  /**
   * Detect popup entry point
   */
  private detectPopupEntry(
    manifest: Record<string, unknown>,
    entryPoints: Record<string, string>
  ): void {
    const popup = manifest.action?.default_popup || manifest.browser_action?.default_popup;
    if (!popup) return;

    const jsFile = this.findAssociatedJS(path.join(this.projectRoot, popup));
    if (jsFile) {
      entryPoints["popup"] = jsFile;
    }
  }

  /**
   * Detect options page entry point
   */
  private detectOptionsEntry(
    manifest: Record<string, unknown>,
    entryPoints: Record<string, string>
  ): void {
    const options = manifest.options_ui?.page || manifest.options_page;
    if (!options) return;

    const jsFile = this.findAssociatedJS(path.join(this.projectRoot, options));
    if (jsFile) {
      entryPoints["options"] = jsFile;
    }
  }

  /**
   * Detect PWA from manifest.json
   */
  private detectPWA(manifestPath: string): ProjectConfig {
    const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    const entryPoints: Record<string, string> = {};

    // Look for service worker
    const swCandidates = [
      "src/service-worker.ts",
      "src/sw.ts",
      "public/service-worker.js",
      "public/sw.js",
    ];

    for (const candidate of swCandidates) {
      const fullPath = path.join(this.projectRoot, candidate);
      if (fs.existsSync(fullPath)) {
        entryPoints["worker"] = fullPath;
        break;
      }
    }

    // Look for main client entry
    const clientCandidates = [
      "src/main.ts",
      "src/index.ts",
      "src/app.ts",
      "src/main.tsx",
      "src/index.tsx",
    ];

    for (const candidate of clientCandidates) {
      const fullPath = path.join(this.projectRoot, candidate);
      if (fs.existsSync(fullPath)) {
        entryPoints["client"] = fullPath;
        break;
      }
    }

    return {
      type: "pwa",
      entryPoints,
      contextMapping: {
        worker: "Service Worker",
        client: "Client App",
      },
      metadata: {
        name: manifest.name || manifest.short_name,
        version: "1.0.0",
        description: manifest.description,
      },
    };
  }

  /**
   * Detect Electron app
   */
  private detectElectron(packageJson: any): ProjectConfig {
    const entryPoints: Record<string, string> = {};

    // Main process
    const mainCandidates = [
      packageJson.main,
      "src/main/index.ts",
      "src/electron/main.ts",
      "electron/main.ts",
      "main.ts",
    ].filter(Boolean);

    for (const candidate of mainCandidates) {
      const fullPath = path.join(this.projectRoot, candidate!);
      if (fs.existsSync(fullPath) || fs.existsSync(fullPath.replace(/\.js$/, ".ts"))) {
        entryPoints["main"] = fs.existsSync(fullPath) ? fullPath : fullPath.replace(/\.js$/, ".ts");
        break;
      }
    }

    // Renderer process
    const rendererCandidates = [
      "src/renderer/index.tsx",
      "src/renderer/index.ts",
      "src/index.tsx",
      "src/index.ts",
    ];

    for (const candidate of rendererCandidates) {
      const fullPath = path.join(this.projectRoot, candidate);
      if (fs.existsSync(fullPath)) {
        entryPoints["renderer"] = fullPath;
        break;
      }
    }

    return {
      type: "electron",
      entryPoints,
      contextMapping: {
        main: "Main Process",
        renderer: "Renderer Process",
      },
      metadata: {
        name: packageJson.name,
        version: packageJson.version,
        description: packageJson.description,
      },
    };
  }

  /**
   * Detect WebSocket/server app with content analysis and confidence scoring
   */
  private detectWebSocketApp(packageJson: any): ProjectConfig {
    const entryPoints: Record<string, string> = {};
    const contextMapping: Record<string, string> = {};

    // Server entry point with content analysis
    const serverCandidates = [
      "src/server.ts",
      "src/server.js",
      "src/index.ts",
      "src/index.js",
      "src/main.ts",
      "src/main.js",
      "src/app.ts",
      "src/app.js",
      "server.ts",
      "server.js",
      "index.ts",
      "index.js",
    ];

    const scoredServers = this.scoreServerCandidates(serverCandidates);
    if (scoredServers.length > 0) {
      const best = scoredServers[0]!;
      entryPoints["server"] = best.path;

      // Add context based on detected frameworks
      if (best.hasWebSocket) {
        contextMapping["server"] = "WebSocket Server";
      } else if (best.hasHTTP) {
        contextMapping["server"] = "HTTP Server";
      } else {
        contextMapping["server"] = "Server";
      }
    }

    // Client entry point (if exists)
    const clientCandidates = [
      "src/client/index.ts",
      "src/client/index.js",
      "src/client.ts",
      "src/client.js",
      "client/index.ts",
      "client/index.js",
    ];

    for (const candidate of clientCandidates) {
      const fullPath = path.join(this.projectRoot, candidate);
      if (fs.existsSync(fullPath)) {
        entryPoints["client"] = fullPath;
        contextMapping["client"] = "Client";
        break;
      }
    }

    return {
      type: "websocket-app",
      entryPoints,
      contextMapping:
        Object.keys(contextMapping).length > 0
          ? contextMapping
          : {
              server: "Server",
              client: "Client",
            },
      metadata: {
        name: packageJson.name,
        version: packageJson.version,
        description: packageJson.description,
      },
    };
  }

  /**
   * Score server candidates based on content analysis
   * Returns sorted array with highest confidence first
   */
  private scoreServerCandidates(candidates: string[]): Array<{
    path: string;
    score: number;
    hasWebSocket: boolean;
    hasHTTP: boolean;
    framework: string | null;
  }> {
    const scored: Array<{
      path: string;
      score: number;
      hasWebSocket: boolean;
      hasHTTP: boolean;
      framework: string | null;
    }> = [];

    for (const candidate of candidates) {
      const fullPath = path.join(this.projectRoot, candidate);
      if (!fs.existsSync(fullPath)) continue;

      try {
        const content = fs.readFileSync(fullPath, "utf-8");
        let score = 0;
        let hasWebSocket = false;
        let hasHTTP = false;
        let framework: string | null = null;

        // Framework-specific patterns
        const patterns = {
          // Bun WebSocket server
          bunWebSocket: /Bun\.serve\s*\([^)]*websocket\s*:/i,
          bunHTTP: /Bun\.serve\s*\(/i,

          // Node ws library
          wsServer: /new\s+WebSocket\.Server/i,
          wsImport: /from\s+['"]ws['"]/,

          // Socket.io
          socketIO: /io\s*\(|require\s*\(\s*['"]socket\.io['"]\s*\)/i,

          // Elysia
          elysia: /new\s+Elysia\s*\(|\.ws\s*\(/i,
          elysiaImport: /from\s+['"]elysia['"]/,

          // Express
          express: /express\s*\(\)|app\.listen/i,
          expressWs: /expressWs\s*\(/i,

          // Generic HTTP server
          httpServer: /createServer|app\.listen|server\.listen/i,

          // Generic WebSocket patterns
          webSocket: /WebSocket|websocket|\.ws\s*\(|wss\s*:/i,
        };

        // Detect frameworks and score
        if (patterns.bunWebSocket.test(content)) {
          score += 15;
          hasWebSocket = true;
          hasHTTP = true;
          framework = "Bun";
        } else if (patterns.bunHTTP.test(content)) {
          score += 10;
          hasHTTP = true;
          framework = "Bun";
        }

        if (patterns.wsServer.test(content) || patterns.wsImport.test(content)) {
          score += 12;
          hasWebSocket = true;
          framework = framework || "ws";
        }

        if (patterns.socketIO.test(content)) {
          score += 12;
          hasWebSocket = true;
          framework = framework || "socket.io";
        }

        if (patterns.elysia.test(content) || patterns.elysiaImport.test(content)) {
          score += 10;
          hasHTTP = true;
          framework = framework || "Elysia";
        }

        if (patterns.elysiaImport.test(content) && patterns.webSocket.test(content)) {
          score += 8;
          hasWebSocket = true;
        }

        if (patterns.express.test(content)) {
          score += 8;
          hasHTTP = true;
          framework = framework || "Express";
        }

        if (patterns.expressWs.test(content)) {
          score += 5;
          hasWebSocket = true;
        }

        if (patterns.httpServer.test(content) && !hasHTTP) {
          score += 5;
          hasHTTP = true;
        }

        if (patterns.webSocket.test(content) && !hasWebSocket) {
          score += 3;
          hasWebSocket = true;
        }

        // Bonus points for likely entry points
        if (/\.listen\s*\(/.test(content)) {
          score += 5;
        }

        if (/export\s+default/.test(content)) {
          score += 3;
        }

        // File name bonuses
        if (candidate.includes("server")) {
          score += 3;
        }

        if (candidate === "src/index.ts" || candidate === "src/index.js") {
          score += 2;
        }

        // Only include files with some indication of being a server
        if (score > 0) {
          scored.push({ path: fullPath, score, hasWebSocket, hasHTTP, framework });
        }
      } catch (_error) {}
    }

    // Sort by score descending
    return scored.sort((a, b) => b.score - a.score);
  }

  /**
   * Fallback: Generic TypeScript project
   * Uses tsconfig.json to find entry points
   */
  private detectGenericProject(): ProjectConfig {
    const entryPoints: Record<string, string> = {};

    // Try to find tsconfig.json
    const tsConfigPath = path.join(this.projectRoot, "tsconfig.json");
    if (fs.existsSync(tsConfigPath)) {
      try {
        const tsConfig = JSON.parse(fs.readFileSync(tsConfigPath, "utf-8"));

        // Check for entry points in various locations
        if (tsConfig.files && Array.isArray(tsConfig.files)) {
          tsConfig.files.forEach((file: string, idx: number) => {
            const fullPath = path.join(this.projectRoot, file);
            if (fs.existsSync(fullPath)) {
              entryPoints[`module${idx + 1}`] = fullPath;
            }
          });
        }
      } catch (_error) {}
    }

    // If no entry points found, scan src directory
    if (Object.keys(entryPoints).length === 0) {
      const commonEntries = ["src/index.ts", "src/main.ts", "src/app.ts", "index.ts", "main.ts"];

      for (const candidate of commonEntries) {
        const fullPath = path.join(this.projectRoot, candidate);
        if (fs.existsSync(fullPath)) {
          entryPoints["main"] = fullPath;
          break;
        }
      }
    }

    // Get metadata from package.json
    const packageJsonPath = path.join(this.projectRoot, "package.json");
    let metadata: ProjectConfig["metadata"] = { name: "Unknown Project" };

    if (fs.existsSync(packageJsonPath)) {
      try {
        const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, "utf-8"));
        metadata = {
          name: packageJson.name,
          version: packageJson.version,
          description: packageJson.description,
        };
      } catch (_error) {}
    }

    return {
      type: "generic",
      entryPoints,
      metadata,
    };
  }

  /**
   * Find source file from manifest reference
   */
  private findSourceFile(manifestPath: string): string {
    const candidates = [
      path.join(this.projectRoot, manifestPath),
      path.join(this.projectRoot, manifestPath.replace(/\.js$/, ".ts")),
      path.join(this.projectRoot, "src", manifestPath),
      path.join(this.projectRoot, "src", manifestPath.replace(/\.js$/, ".ts")),
      path.join(this.projectRoot, "src", manifestPath.replace(/\.js$/, ".tsx")),
    ];

    for (const candidate of candidates) {
      if (fs.existsSync(candidate)) {
        return candidate;
      }
    }

    return path.join(this.projectRoot, manifestPath);
  }

  /**
   * Find associated JavaScript/TypeScript file for an HTML file
   */
  private findAssociatedJS(htmlPath: string): string | null {
    if (!fs.existsSync(htmlPath)) {
      return null;
    }

    // Read HTML and look for script tags
    const html = fs.readFileSync(htmlPath, "utf-8");
    const scriptMatch = html.match(/<script[^>]+src=["']([^"']+)["']/i);

    if (scriptMatch?.[1]) {
      const scriptPath = scriptMatch[1];
      const fullPath = path.resolve(path.dirname(htmlPath), scriptPath);

      if (fs.existsSync(fullPath)) return fullPath;
      if (fs.existsSync(fullPath.replace(/\.js$/, ".ts"))) {
        return fullPath.replace(/\.js$/, ".ts");
      }
      if (fs.existsSync(fullPath.replace(/\.js$/, ".tsx"))) {
        return fullPath.replace(/\.js$/, ".tsx");
      }
    }

    // Fallback: convention-based files
    const baseName = path.basename(htmlPath, ".html");
    const dir = path.dirname(htmlPath);

    const candidates = [
      path.join(dir, `${baseName}.ts`),
      path.join(dir, `${baseName}.tsx`),
      path.join(dir, `${baseName}.js`),
      path.join(dir, "index.ts"),
      path.join(dir, "index.tsx"),
    ];

    for (const candidate of candidates) {
      if (fs.existsSync(candidate)) {
        return candidate;
      }
    }

    return null;
  }
}

/**
 * Detect project configuration from project root
 */
export function detectProjectConfig(projectRoot: string): ProjectConfig {
  const detector = new ProjectDetector(projectRoot);
  return detector.detect();
}
