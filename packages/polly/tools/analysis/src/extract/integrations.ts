// External integration detection - find external APIs, services, etc.

import * as path from "node:path";
import type { Expression, Node, SourceFile } from "typescript-7/ast";
import {
  isCallExpression,
  isIdentifier,
  isNewExpression,
  isObjectLiteralExpression,
  isPropertyAssignment,
  isStringLiteral,
  isTemplateExpression,
} from "typescript-7/ast/is";
import {
  type AnalysisProgram,
  type AnalysisSource,
  forEachDescendant,
  importDeclarations,
  jsDocDescription,
  jsDocs,
  moduleSpecifierValue,
  objectProperty,
  startLine,
  textOf,
  withProgram,
} from "../program";
import type { ExternalIntegration } from "../types/architecture";
import { isOffSurfacePath } from "./source-surface";

export class IntegrationAnalyzer {
  private tsConfigPath: string;
  private projectRoot: string;
  private internalPackages: ReadonlySet<string>;

  /**
   * `internalPackages`: the names of the project's own packages (a
   * workspace's packages, the project itself). Importing one is code of
   * the app, not an external dependency.
   */
  constructor(tsConfigPath: string, internalPackages: Iterable<string> = []) {
    this.tsConfigPath = tsConfigPath;
    this.projectRoot = path.dirname(path.resolve(tsConfigPath));
    this.internalPackages = new Set(internalPackages);
  }

  /**
   * The files whose calls are the app's own. A test, spec or e2e file that
   * fetches the app's server is a client of the app, not an integration of it.
   * Same rule as `HandlerExtractor.isOffSurfaceScannable`, matched against the
   * path inside the project so a project that itself sits under a `__tests__`
   * fixture directory still counts.
   */
  private applicationSourceFiles(program: AnalysisProgram): SourceFile[] {
    return program.sourceFiles.filter(
      (file) => !isOffSurfacePath(`/${path.relative(this.projectRoot, file.fileName)}`)
    );
  }

  /**
   * Analyze external integrations in the codebase. With no `source`, opens
   * (and closes) a session of its own; a passed source stays the caller's.
   */
  analyzeIntegrations(source?: AnalysisSource): Promise<ExternalIntegration[]> {
    return withProgram(this.tsConfigPath, source, (program) =>
      this.integrationsIn(this.applicationSourceFiles(program))
    );
  }

  private integrationsIn(files: readonly SourceFile[]): ExternalIntegration[] {
    const integrations = new Map<string, ExternalIntegration>();

    // Find all fetch() calls
    const fetchCalls = this.findFetchCalls(files);
    for (const call of fetchCalls) {
      this.addOrMergeIntegration(integrations, this.createAPIIntegration(call));
    }

    // Find WebSocket connections
    const websockets = this.findWebSockets(files);
    for (const ws of websockets) {
      this.addOrMergeIntegration(integrations, this.createWebSocketIntegration(ws));
    }

    // Find external script imports
    const externalScripts = this.findExternalScripts(files);
    for (const script of externalScripts) {
      this.addOrMergeIntegration(integrations, script);
    }

    return Array.from(integrations.values());
  }

  /**
   * Find all fetch() API calls
   */
  private findFetchCalls(files: readonly SourceFile[]): Array<{
    url: string;
    method: string;
    file: string;
    line: number;
    description?: string;
  }> {
    const calls: Array<{
      url: string;
      method: string;
      file: string;
      line: number;
      description?: string;
    }> = [];

    for (const sourceFile of files) {
      forEachDescendant(sourceFile, (node) => {
        this.processFetchCall(node, sourceFile, calls);
      });
    }

    return calls;
  }

  /**
   * Process a node that might be a fetch call
   */
  private processFetchCall(
    node: Node,
    sourceFile: SourceFile,
    calls: Array<{
      url: string;
      method: string;
      file: string;
      line: number;
      description?: string;
    }>
  ): void {
    if (!isCallExpression(node)) {
      return;
    }

    const expression = node.expression;
    if (!this.isFetchCall(expression)) {
      return;
    }

    const args = node.arguments;
    if (args.length === 0) {
      return;
    }

    const firstArg = args[0];
    if (!firstArg) return;

    const url = this.extractURLFromArg(firstArg);
    if (!url) {
      return;
    }

    const method = this.extractMethodFromOptions(args);
    const description = this.extractJSDocDescription(node);

    calls.push({
      url,
      method,
      file: sourceFile.fileName,
      line: startLine(node, sourceFile),
      description,
    });
  }

  /**
   * Check if expression is a fetch call
   */
  private isFetchCall(expression: Node): boolean {
    return isIdentifier(expression) && textOf(expression) === "fetch";
  }

  /**
   * Extract URL from fetch argument
   */
  private extractURLFromArg(urlArg: Node): string | null {
    if (isStringLiteral(urlArg)) {
      return urlArg.text;
    }

    if (isTemplateExpression(urlArg)) {
      return this.extractBaseURL(textOf(urlArg));
    }

    return null;
  }

  /**
   * Extract HTTP method from fetch options
   */
  private extractMethodFromOptions(args: readonly Expression[]): string {
    const defaultMethod = "GET";

    if (args.length <= 1) {
      return defaultMethod;
    }

    const optionsArg = args[1];
    if (!optionsArg || !isObjectLiteralExpression(optionsArg)) {
      return defaultMethod;
    }

    const methodProp = objectProperty(optionsArg, "method");
    if (!methodProp || !isPropertyAssignment(methodProp)) {
      return defaultMethod;
    }

    const initializer = methodProp.initializer;
    if (!isStringLiteral(initializer)) {
      return defaultMethod;
    }

    return initializer.text.toUpperCase();
  }

  /**
   * Find WebSocket connections
   */
  private findWebSockets(files: readonly SourceFile[]): Array<{
    url: string;
    file: string;
    line: number;
    description?: string;
  }> {
    const websockets: Array<{
      url: string;
      file: string;
      line: number;
      description?: string;
    }> = [];

    for (const sourceFile of files) {
      forEachDescendant(sourceFile, (node) => {
        if (isNewExpression(node)) {
          const expression = node.expression;

          // Check for new WebSocket()
          if (isIdentifier(expression) && textOf(expression) === "WebSocket") {
            const first = node.arguments?.[0];
            if (first && isStringLiteral(first)) {
              const url = first.text;
              const description = this.extractJSDocDescription(node);

              websockets.push({
                url,
                file: sourceFile.fileName,
                line: startLine(node, sourceFile),
                description,
              });
            }
          }
        }
      });
    }

    return websockets;
  }

  /**
   * Find external script dependencies (from imports)
   */
  private findExternalScripts(files: readonly SourceFile[]): ExternalIntegration[] {
    const scripts: ExternalIntegration[] = [];
    const seen = new Set<string>();

    for (const sourceFile of files) {
      this.extractExternalImportsFromFile(sourceFile, scripts, seen);
    }

    return scripts;
  }

  /**
   * Extract external imports from a single file
   */
  private extractExternalImportsFromFile(
    sourceFile: SourceFile,
    scripts: ExternalIntegration[],
    seen: Set<string>
  ): void {
    for (const importDecl of importDeclarations(sourceFile)) {
      const moduleSpecifier = moduleSpecifierValue(importDecl);

      if (moduleSpecifier !== undefined && this.isExternalImport(moduleSpecifier)) {
        const packageName = this.extractPackageName(moduleSpecifier);

        if (packageName && !seen.has(packageName) && !this.internalPackages.has(packageName)) {
          seen.add(packageName);
          scripts.push(this.createExternalScriptIntegration(packageName, sourceFile));
        }
      }
    }
  }

  /**
   * Check if import is external (not relative)
   */
  private isExternalImport(moduleSpecifier: string): boolean {
    return !moduleSpecifier.startsWith(".") && !moduleSpecifier.startsWith("/");
  }

  /**
   * Extract package name from module specifier
   */
  private extractPackageName(moduleSpecifier: string): string | undefined {
    // Handle scoped packages (@org/package)
    if (moduleSpecifier.startsWith("@")) {
      return moduleSpecifier.split("/").slice(0, 2).join("/");
    }
    // Handle regular packages
    return moduleSpecifier.split("/")[0];
  }

  /**
   * Create external script integration object
   */
  private createExternalScriptIntegration(
    packageName: string,
    sourceFile: SourceFile
  ): ExternalIntegration {
    return {
      type: "external-script",
      name: packageName,
      technology: "npm package",
      usedIn: [sourceFile.fileName],
      description: `External dependency: ${packageName}`,
    };
  }

  /**
   * Create API integration from fetch call
   */
  private createAPIIntegration(call: {
    url: string;
    method: string;
    file: string;
    line: number;
    description?: string;
  }): ExternalIntegration {
    // Extract base URL
    const baseURL = this.extractBaseURL(call.url);

    // Infer name from URL
    const name = this.inferAPIName(baseURL);

    return {
      type: "api",
      name,
      technology: "REST API",
      url: baseURL,
      usedIn: [call.file],
      description: call.description || `External API: ${name}`,
      calls: [
        {
          method: call.method,
          endpoint: call.url,
          location: {
            file: call.file,
            line: call.line,
          },
          description: call.description,
        },
      ],
    };
  }

  /**
   * Create WebSocket integration
   */
  private createWebSocketIntegration(ws: {
    url: string;
    file: string;
    line: number;
    description?: string;
  }): ExternalIntegration {
    const name = this.inferAPIName(ws.url);

    return {
      type: "websocket",
      name,
      technology: "WebSocket",
      url: ws.url,
      usedIn: [ws.file],
      description: ws.description || `WebSocket connection: ${name}`,
    };
  }

  /**
   * Extract base URL from full URL or template
   */
  private extractBaseURL(url: string): string {
    // Remove template parts
    let cleanUrl = url.replace(/\$\{[^}]+\}/g, "");
    cleanUrl = cleanUrl.replace(/`/g, "");

    try {
      const parsed = new URL(cleanUrl);
      return `${parsed.protocol}//${parsed.host}`;
    } catch {
      // If parsing fails, try to extract domain
      const match = cleanUrl.match(/https?:\/\/([^/]+)/);
      return match ? match[0] : cleanUrl;
    }
  }

  /**
   * Infer API name from URL
   */
  private inferAPIName(url: string): string {
    try {
      const parsed = new URL(url);
      const hostname = parsed.hostname;

      // Remove www. prefix
      const cleanHost = hostname.replace(/^www\./, "");

      // Take first part of domain
      const parts = cleanHost.split(".");
      if (parts.length > 0 && parts[0]) {
        // Capitalize first letter
        return `${parts[0].charAt(0).toUpperCase() + parts[0].slice(1)} API`;
      }
    } catch {
      // Fallback
    }

    return "External API";
  }

  /**
   * Add or merge integration into map
   */
  private addOrMergeIntegration(
    map: Map<string, ExternalIntegration>,
    integration: ExternalIntegration
  ): void {
    const key = `${integration.type}:${integration.name}`;

    if (map.has(key)) {
      const existing = map.get(key);
      if (!existing) return;

      // Merge usedIn
      existing.usedIn = [...new Set([...existing.usedIn, ...integration.usedIn])];

      // Merge calls
      if (integration.calls && existing.calls) {
        existing.calls.push(...integration.calls);
      } else if (integration.calls) {
        existing.calls = integration.calls;
      }
    } else {
      map.set(key, integration);
    }
  }

  /**
   * Extract JSDoc description from node
   */
  private extractJSDocDescription(node: Node): string | undefined {
    const firstDoc = jsDocs(node)[0];
    if (!firstDoc) return undefined;

    const comment = jsDocDescription(firstDoc).trim();
    return comment || undefined;
  }
}
