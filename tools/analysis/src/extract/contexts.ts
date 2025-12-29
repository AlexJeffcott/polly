// Context analysis - analyze individual execution contexts

import { Node, Project } from "ts-morph";
import type { ComponentInfo, ContextInfo } from "../types/architecture";
import type { MessageHandler } from "../types/core";

export class ContextAnalyzer {
  private project: Project;

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
  }

  /**
   * Analyze a specific context given its entry point
   */
  analyzeContext(contextType: string, entryPoint: string, handlers: MessageHandler[]): ContextInfo {
    const sourceFile = this.project.getSourceFile(entryPoint);

    if (!sourceFile) {
      throw new Error(`Could not find source file: ${entryPoint}`);
    }

    // Extract Chrome API usage
    const chromeAPIs = this.extractChromeAPIs(sourceFile);

    // Extract dependencies
    const dependencies = this.extractDependencies(sourceFile);

    // Extract JSDoc description
    const description = this.extractDescription(sourceFile);

    // Extract components (for UI contexts)
    const components = this.isUIContext(contextType)
      ? this.extractComponents(sourceFile)
      : undefined;

    // Filter handlers for this context
    const contextHandlers = handlers.filter((h) => h.node === contextType);

    return {
      type: contextType,
      entryPoint,
      handlers: contextHandlers,
      chromeAPIs,
      externalAPIs: [], // Will be filled by integration analyzer
      ...(components ? { components } : {}),
      dependencies,
      ...(description ? { description } : {}),
    };
  }

  /**
   * Extract Chrome API usage from source file
   */
  private extractChromeAPIs(sourceFile: any): string[] {
    const apis = new Set<string>();

    sourceFile.forEachDescendant((node: any) => {
      if (Node.isPropertyAccessExpression(node)) {
        const text = node.getText();

        // Match chrome.* API calls
        if (text.startsWith("chrome.")) {
          // Extract API namespace (e.g., "chrome.tabs", "chrome.storage.local")
          const match = text.match(/^chrome\.([^.(]+(?:\.[^.(]+)?)/);
          const api = match?.[1];
          if (api) {
            apis.add(api);
          }
        }

        // Also match browser.* for Firefox compatibility
        if (text.startsWith("browser.")) {
          const match = text.match(/^browser\.([^.(]+(?:\.[^.(]+)?)/);
          const api = match?.[1];
          if (api) {
            apis.add(api);
          }
        }

        // Match bus.adapters.* pattern (framework abstraction over Chrome APIs)
        // e.g., bus.adapters.storage.get() -> storage
        //       bus.adapters.tabs.query() -> tabs
        if (text.includes("bus.adapters.")) {
          const match = text.match(/bus\.adapters\.([^.(]+)/);
          const api = match?.[1];
          if (api) {
            apis.add(api);
          }
        }
      }
    });

    return Array.from(apis).sort();
  }

  /**
   * Extract import dependencies
   */
  private extractDependencies(sourceFile: any): string[] {
    const deps: string[] = [];

    for (const importDecl of sourceFile.getImportDeclarations()) {
      const moduleSpecifier = importDecl.getModuleSpecifierValue();
      deps.push(moduleSpecifier);
    }

    return deps;
  }

  /**
   * Extract JSDoc description from file
   */
  private extractDescription(sourceFile: any): string | undefined {
    // Look for file-level JSDoc comment
    const firstStatement = sourceFile.getStatements()[0];
    if (!firstStatement) return undefined;

    const leadingComments = firstStatement.getLeadingCommentRanges();
    if (leadingComments.length === 0) return undefined;

    const comment = leadingComments[0].getText();

    // Extract description from JSDoc
    const descMatch = comment.match(/@description\s+(.+?)(?:\n|$)/s);
    if (descMatch) {
      return descMatch[1].trim();
    }

    // Or just take the first line of the comment
    const lines = comment
      .split("\n")
      .map((l: string) => l.replace(/^[\s*]+/, "").trim())
      .filter((l: string) => l && !l.startsWith("@"));

    return lines[0] || undefined;
  }

  /**
   * Extract React/Preact components from source file
   */
  private extractComponents(sourceFile: any): ComponentInfo[] {
    const components: ComponentInfo[] = [];

    sourceFile.forEachDescendant((node: any) => {
      // Function components
      if (Node.isFunctionDeclaration(node)) {
        const name = node.getName();
        if (name && this.looksLikeComponent(name, node)) {
          const description = this.extractJSDocDescription(node);
          components.push({
            name,
            type: "function",
            filePath: sourceFile.getFilePath(),
            line: node.getStartLineNumber(),
            props: this.extractProps(node),
            ...(description ? { description } : {}),
          });
        }
      }

      // Arrow function components (const Foo = () => ...)
      if (Node.isVariableDeclaration(node)) {
        const name = node.getName();
        const initializer = node.getInitializer();

        if (
          name &&
          initializer &&
          (Node.isArrowFunction(initializer) || Node.isFunctionExpression(initializer))
        ) {
          if (this.looksLikeComponent(name, initializer)) {
            const description = this.extractJSDocDescription(node);
            components.push({
              name,
              type: "function",
              filePath: sourceFile.getFilePath(),
              line: node.getStartLineNumber(),
              props: this.extractProps(initializer),
              ...(description ? { description } : {}),
            });
          }
        }
      }

      // Class components
      if (Node.isClassDeclaration(node)) {
        const name = node.getName();
        if (name && this.looksLikeClassComponent(node)) {
          const description = this.extractJSDocDescription(node);
          components.push({
            name,
            type: "class",
            filePath: sourceFile.getFilePath(),
            line: node.getStartLineNumber(),
            props: this.extractPropsFromClass(node),
            ...(description ? { description } : {}),
          });
        }
      }
    });

    return components;
  }

  /**
   * Check if a function looks like a React/Preact component
   */
  private looksLikeComponent(name: string, node: any): boolean {
    // Component names should start with uppercase
    if (!/^[A-Z]/.test(name)) return false;

    // Check if it returns JSX
    const body = node.getBody();
    if (!body) return false;

    let hasJSX = false;

    if (Node.isBlock(body)) {
      body.forEachDescendant((child: any) => {
        if (Node.isJsxElement(child) || Node.isJsxSelfClosingElement(child)) {
          hasJSX = true;
        }
      });
    } else {
      // Arrow function with implicit return
      if (Node.isJsxElement(body) || Node.isJsxSelfClosingElement(body)) {
        hasJSX = true;
      }
    }

    return hasJSX;
  }

  /**
   * Check if a class looks like a React component
   */
  private looksLikeClassComponent(node: any): boolean {
    const extendedTypes = node.getExtends();
    if (!extendedTypes) return false;

    const extendsText = extendedTypes.getText();
    return /Component|PureComponent/.test(extendsText);
  }

  /**
   * Extract props from function component
   */
  private extractProps(node: any): string[] {
    const params = node.getParameters();
    if (params.length === 0) return [];

    const propsParam = params[0];
    const type = propsParam.getType();

    const props: string[] = [];
    for (const prop of type.getProperties()) {
      props.push(prop.getName());
    }

    return props;
  }

  /**
   * Extract props from class component
   */
  private extractPropsFromClass(node: any): string[] {
    const extendedTypes = node.getExtends();
    if (!extendedTypes) return [];

    const typeArgs = extendedTypes.getType().getTypeArguments();
    if (typeArgs.length === 0) return [];

    const propsType = typeArgs[0];
    const props: string[] = [];

    for (const prop of propsType.getProperties()) {
      props.push(prop.getName());
    }

    return props;
  }

  /**
   * Extract JSDoc description from node
   */
  private extractJSDocDescription(node: any): string | undefined {
    const jsDocs = node.getJsDocs();
    if (jsDocs.length === 0) return undefined;

    const description = jsDocs[0].getDescription().trim();
    return description || undefined;
  }

  /**
   * Check if context is a UI context
   */
  private isUIContext(contextType: string): boolean {
    return ["popup", "options", "devtools"].includes(contextType);
  }
}
