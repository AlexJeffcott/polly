// Manifest.json parser for Chrome extensions

import * as fs from "node:fs";
import * as path from "node:path";
import {
  readBoolean,
  readNumber,
  readRecord,
  readRecordArray,
  readString,
  readStringArray,
} from "../../../../src/shared/lib/guards";
import type { ManifestInfo } from "../types/architecture";

/**
 * Parse manifest.json and extract context information
 */
export class ManifestParser {
  private manifestPath: string;
  private manifestData: Record<string, unknown> | null;
  private baseDir: string;

  constructor(projectRoot: string, optional = false) {
    this.baseDir = projectRoot;
    this.manifestPath = path.join(projectRoot, "manifest.json");

    if (!fs.existsSync(this.manifestPath)) {
      if (optional) {
        this.manifestData = null;
        return;
      }
      throw new Error(`manifest.json not found at ${this.manifestPath}`);
    }

    try {
      const content = fs.readFileSync(this.manifestPath, "utf-8");
      this.manifestData = readRecord(JSON.parse(content)) ?? null;
    } catch (error) {
      throw new Error(`Failed to parse manifest.json: ${error}`);
    }
  }

  /**
   * Check if manifest.json exists and was loaded
   */
  hasManifest(): boolean {
    return this.manifestData !== null;
  }

  /**
   * Parse manifest and extract all information
   */
  parse(): ManifestInfo {
    if (!this.manifestData) {
      throw new Error(
        "Cannot parse manifest: manifest.json not loaded. Use hasManifest() to check availability."
      );
    }

    const manifest = this.manifestData;

    return {
      name: readString(manifest["name"]) || "Unknown Extension",
      version: readString(manifest["version"]) || "0.0.0",
      description: readString(manifest["description"]),
      manifestVersion: readNumber(manifest["manifest_version"]) || 2,
      background: this.parseBackground(),
      contentScripts: this.parseContentScripts(),
      popup: this.parsePopup(),
      options: this.parseOptions(),
      devtools: this.parseDevtools(),
      permissions: readStringArray(manifest["permissions"]) ?? [],
      hostPermissions: readStringArray(manifest["host_permissions"]) ?? [],
    };
  }

  /**
   * Get context entry points from manifest
   */
  getContextEntryPoints(): Record<string, string> {
    if (!this.manifestData) {
      return {};
    }

    const entryPoints: Record<string, string> = {};

    this.addBackgroundEntryPoint(entryPoints);
    this.addContentScriptEntryPoint(entryPoints);
    this.addPopupEntryPoint(entryPoints);
    this.addOptionsEntryPoint(entryPoints);
    this.addDevtoolsEntryPoint(entryPoints);

    return entryPoints;
  }

  private addBackgroundEntryPoint(entryPoints: Record<string, string>): void {
    const background = this.parseBackground();
    if (!background) return;

    const entryFile = background.files[0];
    if (entryFile) {
      entryPoints["background"] = this.findSourceFile(entryFile);
    }
  }

  private addContentScriptEntryPoint(entryPoints: Record<string, string>): void {
    const contentScripts = this.parseContentScripts();
    if (!contentScripts || contentScripts.length === 0) return;

    const firstScript = contentScripts[0]?.js[0];
    if (firstScript) {
      entryPoints["content"] = this.findSourceFile(firstScript);
    }
  }

  private addPopupEntryPoint(entryPoints: Record<string, string>): void {
    const popup = this.parsePopup();
    if (!popup) return;

    const jsPath = this.findAssociatedJS(this.findSourceHtml(popup.html));
    if (jsPath) {
      entryPoints["popup"] = jsPath;
    }
  }

  private addOptionsEntryPoint(entryPoints: Record<string, string>): void {
    const options = this.parseOptions();
    if (!options) return;

    const jsPath = this.findAssociatedJS(this.findSourceHtml(options.page));
    if (jsPath) {
      entryPoints["options"] = jsPath;
    }
  }

  private addDevtoolsEntryPoint(entryPoints: Record<string, string>): void {
    const devtools = this.parseDevtools();
    if (!devtools) return;

    const jsPath = this.findAssociatedJS(this.findSourceHtml(devtools.page));
    if (jsPath) {
      entryPoints["devtools"] = jsPath;
    }
  }

  /**
   * Parse background configuration
   */
  private parseBackground(): ManifestInfo["background"] {
    if (!this.manifestData) return undefined;

    const bg = readRecord(this.manifestData["background"]);
    if (!bg) return undefined;

    // Manifest V3 - service worker
    const serviceWorker = readString(bg["service_worker"]);
    if (serviceWorker) {
      return { type: "service_worker", files: [serviceWorker] };
    }

    // Manifest V2 - scripts
    const scripts = readStringArray(bg["scripts"]);
    if (scripts) {
      return { type: "script", files: scripts };
    }

    // Manifest V2 - page
    const page = readString(bg["page"]);
    if (page) {
      return { type: "script", files: [page] };
    }

    return undefined;
  }

  /**
   * Parse content scripts configuration
   */
  private parseContentScripts(): ManifestInfo["contentScripts"] {
    if (!this.manifestData) return undefined;

    const cs = readRecordArray(this.manifestData["content_scripts"]);
    if (!cs) return undefined;

    return cs.map((script) => ({
      matches: readStringArray(script["matches"]) ?? [],
      js: readStringArray(script["js"]) ?? [],
      css: readStringArray(script["css"]),
    }));
  }

  /**
   * Parse popup configuration
   */
  private parsePopup(): ManifestInfo["popup"] {
    if (!this.manifestData) return undefined;

    const action =
      readRecord(this.manifestData["action"]) ?? readRecord(this.manifestData["browser_action"]);
    if (!action) return undefined;

    const popup = readString(action["default_popup"]);
    if (popup) {
      return { html: popup, default: true };
    }

    return undefined;
  }

  /**
   * Parse options configuration
   */
  private parseOptions(): ManifestInfo["options"] {
    if (!this.manifestData) return undefined;

    const options = this.manifestData["options_ui"] || this.manifestData["options_page"];
    if (!options) return undefined;

    if (typeof options === "string") {
      return {
        page: options,
        openInTab: false,
      };
    }

    const optionsObj = readRecord(options);
    const page = readString(optionsObj?.["page"]);
    if (!page) return undefined;
    return {
      page,
      openInTab: readBoolean(optionsObj?.["open_in_tab"]) ?? false,
    };
  }

  /**
   * Parse devtools configuration
   */
  private parseDevtools(): ManifestInfo["devtools"] {
    if (!this.manifestData) return undefined;

    const devtools = readString(this.manifestData["devtools_page"]);
    if (!devtools) return undefined;

    return { page: devtools };
  }

  /**
   * Find source file from manifest reference
   * Tries multiple locations: exact path, src/ directory, .ts extension
   */
  private findSourceFile(manifestPath: string): string {
    const candidates = [
      // Exact path from manifest
      path.join(this.baseDir, manifestPath),
      // Same path with .ts extension
      path.join(this.baseDir, manifestPath.replace(/\.js$/, ".ts")),
      // In src/ directory
      path.join(this.baseDir, "src", manifestPath),
      path.join(this.baseDir, "src", manifestPath.replace(/\.js$/, ".ts")),
      // In src/ with .tsx extension
      path.join(this.baseDir, "src", manifestPath.replace(/\.js$/, ".tsx")),
    ];

    for (const candidate of candidates) {
      if (fs.existsSync(candidate)) {
        return candidate;
      }
    }

    // Fallback to manifest path (will error later if not found)
    return path.join(this.baseDir, manifestPath);
  }

  /**
   * The source HTML page for a manifest page path. The manifest names the
   * built layout (`popup/popup.html`); the page usually lives under `src/`,
   * as `findSourceFile` already allows for scripts.
   */
  private findSourceHtml(manifestPath: string): string {
    const atRoot = path.join(this.baseDir, manifestPath);
    if (fs.existsSync(atRoot)) return atRoot;
    const inSrc = path.join(this.baseDir, "src", manifestPath);
    return fs.existsSync(inSrc) ? inSrc : atRoot;
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

      // Try with and without .js/.ts extension
      if (fs.existsSync(fullPath)) return fullPath;
      if (fs.existsSync(fullPath.replace(/\.js$/, ".ts"))) {
        return fullPath.replace(/\.js$/, ".ts");
      }
      if (fs.existsSync(fullPath.replace(/\.js$/, ".tsx"))) {
        return fullPath.replace(/\.js$/, ".tsx");
      }
    }

    // Fallback: look for convention-based files
    const baseName = path.basename(htmlPath, ".html");
    const dir = path.dirname(htmlPath);

    const candidates = [
      path.join(dir, `${baseName}.ts`),
      path.join(dir, `${baseName}.tsx`),
      path.join(dir, `${baseName}.js`),
      path.join(dir, "index.ts"),
      path.join(dir, "index.tsx"),
      path.join(dir, "index.js"),
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
 * Parse manifest.json and extract information
 */
export function parseManifest(projectRoot: string): ManifestInfo {
  const parser = new ManifestParser(projectRoot);
  return parser.parse();
}

/**
 * Get context entry points from manifest.json
 */
export function getContextEntryPoints(projectRoot: string): Record<string, string> {
  const parser = new ManifestParser(projectRoot);
  return parser.getContextEntryPoints();
}
