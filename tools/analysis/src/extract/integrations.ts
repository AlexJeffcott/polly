// External integration detection - find external APIs, services, etc.

import { Node, Project } from "ts-morph";
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
        if (Node.isCallExpression(node)) {
          const expression = node.getExpression();

          // Check for fetch() calls
          if (Node.isIdentifier(expression) && expression.getText() === "fetch") {
            const args = node.getArguments();
            if (args.length > 0) {
              // Extract URL
              const urlArg = args[0];
              let url: string | null = null;

              if (Node.isStringLiteral(urlArg)) {
                url = urlArg.getLiteralValue();
              } else if (Node.isTemplateExpression(urlArg)) {
                // Try to extract base URL from template
                url = this.extractBaseURL(urlArg.getText());
              }

              if (url) {
                // Extract method
                let method = "GET"; // Default
                if (args.length > 1 && Node.isObjectLiteralExpression(args[1])) {
                  const options = args[1];
                  const methodProp = options.getProperty("method");
                  if (methodProp && Node.isPropertyAssignment(methodProp)) {
                    const initializer = methodProp.getInitializer();
                    if (initializer && Node.isStringLiteral(initializer)) {
                      method = initializer.getLiteralValue().toUpperCase();
                    }
                  }
                }

                // Extract description from JSDoc
                const description = this.extractJSDocDescription(node);

                calls.push({
                  url,
                  method,
                  file: sourceFile.getFilePath(),
                  line: node.getStartLineNumber(),
                  description,
                });
              }
            }
          }
        }
      });
    }

    return calls;
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
      for (const importDecl of sourceFile.getImportDeclarations()) {
        const moduleSpecifier = importDecl.getModuleSpecifierValue();

        // Only consider external packages (not relative imports)
        if (!moduleSpecifier.startsWith(".") && !moduleSpecifier.startsWith("/")) {
          // Extract package name (handle scoped packages)
          const packageName = moduleSpecifier.startsWith("@")
            ? moduleSpecifier.split("/").slice(0, 2).join("/")
            : moduleSpecifier.split("/")[0];

          if (packageName && !seen.has(packageName)) {
            seen.add(packageName);

            scripts.push({
              type: "external-script",
              name: packageName,
              technology: "npm package",
              usedIn: [sourceFile.getFilePath()],
              description: `External dependency: ${packageName}`,
            });
          }
        }
      }
    }

    return scripts;
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
    url = url.replace(/\$\{[^}]+\}/g, "");
    url = url.replace(/`/g, "");

    try {
      const parsed = new URL(url);
      return `${parsed.protocol}//${parsed.host}`;
    } catch {
      // If parsing fails, try to extract domain
      const match = url.match(/https?:\/\/([^/]+)/);
      return match ? match[0] : url;
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
      const existing = map.get(key)!;

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
  private extractJSDocDescription(node: any): string | undefined {
    const jsDocs = node.getJsDocs?.() || [];
    if (jsDocs.length === 0) return undefined;

    const comment = jsDocs[0].getDescription().trim();
    return comment || undefined;
  }
}
