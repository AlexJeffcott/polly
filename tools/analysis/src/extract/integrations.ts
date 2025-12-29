// External integration detection - find external APIs, services, etc.

import { Node, Project, type SourceFile } from "ts-morph";
import type { ExternalIntegration } from "../types/architecture";

export class IntegrationAnalyzer {
  private project: Project;

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
  }

  /**
   * Analyze external integrations in the codebase
   */
  analyzeIntegrations(): ExternalIntegration[] {
    const integrations = new Map<string, ExternalIntegration>();

    // Find all fetch() calls
    const fetchCalls = this.findFetchCalls();
    for (const call of fetchCalls) {
      this.addOrMergeIntegration(integrations, this.createAPIIntegration(call));
    }

    // Find WebSocket connections
    const websockets = this.findWebSockets();
    for (const ws of websockets) {
      this.addOrMergeIntegration(integrations, this.createWebSocketIntegration(ws));
    }

    // Find external script imports
    const externalScripts = this.findExternalScripts();
    for (const script of externalScripts) {
      this.addOrMergeIntegration(integrations, script);
    }

    return Array.from(integrations.values());
  }

  /**
   * Find all fetch() API calls
   */
  private findFetchCalls(): Array<{
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

    for (const sourceFile of this.project.getSourceFiles()) {
      sourceFile.forEachDescendant((node) => {
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
    if (!Node.isCallExpression(node)) {
      return;
    }

    const expression = node.getExpression();
    if (!this.isFetchCall(expression)) {
      return;
    }

    const args = node.getArguments();
    if (args.length === 0) {
      return;
    }

    const url = this.extractURLFromArg(args[0]);
    if (!url) {
      return;
    }

    const method = this.extractMethodFromOptions(args);
    const description = this.extractJSDocDescription(node);

    calls.push({
      url,
      method,
      file: sourceFile.getFilePath(),
      line: node.getStartLineNumber(),
      description,
    });
  }

  /**
   * Check if expression is a fetch call
   */
  private isFetchCall(expression: Node): boolean {
    return Node.isIdentifier(expression) && expression.getText() === "fetch";
  }

  /**
   * Extract URL from fetch argument
   */
  private extractURLFromArg(urlArg: Node): string | null {
    if (Node.isStringLiteral(urlArg)) {
      return urlArg.getLiteralValue();
    }

    if (Node.isTemplateExpression(urlArg)) {
      return this.extractBaseURL(urlArg.getText());
    }

    return null;
  }

  /**
   * Extract HTTP method from fetch options
   */
  private extractMethodFromOptions(args: Node[]): string {
    const defaultMethod = "GET";

    if (args.length <= 1) {
      return defaultMethod;
    }

    const optionsArg = args[1];
    if (!Node.isObjectLiteralExpression(optionsArg)) {
      return defaultMethod;
    }

    const methodProp = optionsArg.getProperty("method");
    if (!methodProp || !Node.isPropertyAssignment(methodProp)) {
      return defaultMethod;
    }

    const initializer = methodProp.getInitializer();
    if (!initializer || !Node.isStringLiteral(initializer)) {
      return defaultMethod;
    }

    return initializer.getLiteralValue().toUpperCase();
  }

  /**
   * Find WebSocket connections
   */
  private findWebSockets(): Array<{
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

    for (const sourceFile of this.project.getSourceFiles()) {
      sourceFile.forEachDescendant((node) => {
        if (Node.isNewExpression(node)) {
          const expression = node.getExpression();

          // Check for new WebSocket()
          if (Node.isIdentifier(expression) && expression.getText() === "WebSocket") {
            const args = node.getArguments();
            if (args.length > 0 && Node.isStringLiteral(args[0])) {
              const url = args[0].getLiteralValue();
              const description = this.extractJSDocDescription(node);

              websockets.push({
                url,
                file: sourceFile.getFilePath(),
                line: node.getStartLineNumber(),
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
  private findExternalScripts(): ExternalIntegration[] {
    const scripts: ExternalIntegration[] = [];
    const seen = new Set<string>();

    for (const sourceFile of this.project.getSourceFiles()) {
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
    for (const importDecl of sourceFile.getImportDeclarations()) {
      const moduleSpecifier = importDecl.getModuleSpecifierValue();

      if (this.isExternalImport(moduleSpecifier)) {
        const packageName = this.extractPackageName(moduleSpecifier);

        if (packageName && !seen.has(packageName)) {
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
      usedIn: [sourceFile.getFilePath()],
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
    const jsDocs = node.getJsDocs?.() || [];
    if (jsDocs.length === 0) return undefined;

    const comment = jsDocs[0].getDescription().trim();
    return comment || undefined;
  }
}
