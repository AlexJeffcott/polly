// Component relationship extraction from TypeScript code
// Detects function calls, imports, and dependencies between components

import {
  type ArrowFunction,
  type CallExpression,
  type FunctionDeclaration,
  type FunctionExpression,
  Node,
  type SourceFile,
} from "ts-morph";

/**
 * Represents a relationship between components detected from code analysis
 */
export interface DetectedRelationship {
  /** Source component (handler, service, etc.) */
  from: string;
  /** Target component being called/used */
  to: string;
  /** Description of the relationship */
  description: string;
  /** Technology/method used (e.g., "Function Call", "Import", "SQL", "HTTP") */
  technology?: string;
  /** Confidence level of this detection */
  confidence: "high" | "medium" | "low";
  /** Evidence supporting this detection */
  evidence: string[];
}

/**
 * Extracts component relationships from handler code
 */
export class RelationshipExtractor {
  /**
   * Extract relationships from a function/handler body
   */
  extractFromHandler(
    handlerNode: Node,
    sourceFile: SourceFile,
    handlerName: string
  ): DetectedRelationship[] {
    const relationships: DetectedRelationship[] = [];
    const visited = new Set<string>(); // Prevent infinite recursion

    this.extractFromNode(handlerNode, sourceFile, handlerName, relationships, visited);

    return this.deduplicateRelationships(relationships);
  }

  /**
   * Recursively extract relationships from a node and follow function calls
   */
  private extractFromNode(
    node: Node,
    sourceFile: SourceFile,
    handlerName: string,
    relationships: DetectedRelationship[],
    visited: Set<string>
  ): void {
    // Pattern 1: Function calls within the handler
    node.forEachDescendant((descendant) => {
      if (Node.isCallExpression(descendant)) {
        const expr = descendant.getExpression();

        // Check if this is a local or imported function call that we should follow
        if (Node.isIdentifier(expr)) {
          const functionName = expr.getText();

          // Try to find the function definition in the same file first
          let functionDecl = sourceFile.getFunction(functionName);
          let targetSourceFile = sourceFile;

          // If not in same file, try to resolve from imports (cross-file analysis)
          if (!functionDecl) {
            const resolved = this.resolveImportedFunction(functionName, sourceFile);
            if (resolved) {
              functionDecl = resolved.functionDecl;
              targetSourceFile = resolved.sourceFile;
            }
          }

          if (functionDecl && !visited.has(functionName)) {
            // Mark as visited to prevent infinite recursion
            visited.add(functionName);

            // Recursively extract relationships from the called function
            const body = functionDecl.getBody();
            if (body) {
              this.extractFromNode(body, targetSourceFile, handlerName, relationships, visited);
            }

            // Don't add this as a relationship itself - we're following the call
            return;
          }

          // If we couldn't resolve the function, check if it looks like a service call
          // This catches patterns like getDatabase(), createRepositories()
          if (!functionDecl) {
            const componentFromName = this.inferComponentFromFunctionName(functionName);
            if (componentFromName) {
              relationships.push({
                from: this.toComponentId(handlerName),
                to: componentFromName,
                description: `Calls ${functionName}()`,
                technology: "Function Call",
                confidence: "medium",
                evidence: [`Function call: ${functionName}`],
              });
              return;
            }
          }
        }

        // Check if this call expression has a property access expression
        // (e.g., userService.listUsers())
        if (Node.isPropertyAccessExpression(expr)) {
          const rel = this.extractFromPropertyAccess(expr, handlerName);
          if (rel) {
            relationships.push(rel);
            return; // Don't process further for this call expression
          }
        }

        // Not a local function or property access - try to extract as a relationship
        const rel = this.extractFromFunctionCall(descendant, handlerName, sourceFile);
        if (rel) {
          relationships.push(rel);
        }
      }

      // Pattern 3: Database queries (await db.query, await db.execute)
      if (Node.isAwaitExpression(descendant)) {
        const rel = this.extractFromDatabaseCall(descendant, handlerName);
        if (rel) {
          relationships.push(rel);
        }
      }

      // Pattern 4: Fetch/HTTP calls
      if (Node.isCallExpression(descendant) && descendant.getExpression().getText() === "fetch") {
        const rel = this.extractFromFetchCall(descendant, handlerName);
        if (rel) {
          relationships.push(rel);
        }
      }
    });
  }

  /**
   * Extract relationship from a function call
   */
  private extractFromFunctionCall(
    callExpr: CallExpression,
    handlerName: string,
    sourceFile: SourceFile
  ): DetectedRelationship | null {
    const expr = callExpr.getExpression();
    const exprText = expr.getText();

    // Skip common utility functions and built-ins
    const skipList = [
      "console.",
      "JSON.",
      "Math.",
      "Object.",
      "Array.",
      "String.",
      "Number.",
      "Date.",
      "Promise.",
      "setTimeout",
      "setInterval",
      "clearTimeout",
      "clearInterval",
    ];

    if (skipList.some((skip) => exprText.startsWith(skip))) {
      return null;
    }

    // Extract function name
    let functionName = exprText;
    let targetComponent: string | null = null;

    // Handle property access (e.g., db.getConnection() -> db_client)
    if (Node.isPropertyAccessExpression(expr)) {
      const objectExpr = expr.getExpression();
      const objectName = objectExpr.getText();
      const methodName = expr.getName();

      // Map common patterns to component names
      targetComponent = this.inferComponentFromCall(objectName);

      if (!targetComponent) {
        return null;
      }

      functionName = methodName;
    } else {
      // Direct function call - try to resolve from imports
      targetComponent = this.resolveComponentFromImport(exprText, sourceFile);

      if (!targetComponent) {
        return null;
      }
    }

    return {
      from: this.toComponentId(handlerName),
      to: targetComponent,
      description: `Calls ${functionName}()`,
      technology: "Function Call",
      confidence: "high",
      evidence: [`Function call: ${exprText}`],
    };
  }

  /**
   * Extract relationship from property access chain
   * Handles both simple (obj.method) and nested (obj.prop.method) patterns
   */
  private extractFromPropertyAccess(
    propAccess: Node,
    handlerName: string
  ): DetectedRelationship | null {
    if (!Node.isPropertyAccessExpression(propAccess)) {
      return null;
    }

    const fullChain = propAccess.getText();
    const methodName = propAccess.getName();

    // Extract the root object from potentially nested property access
    // e.g., repositories.users.create -> repositories
    let rootObject = propAccess.getExpression();
    while (Node.isPropertyAccessExpression(rootObject)) {
      rootObject = rootObject.getExpression();
    }

    const objectName = rootObject.getText();

    // Map object name to component name
    const targetComponent = this.inferComponentFromCall(objectName);

    if (!targetComponent) {
      return null;
    }

    return {
      from: this.toComponentId(handlerName),
      to: targetComponent,
      description: `Calls ${methodName}()`,
      technology: "Function Call",
      confidence: "high",
      evidence: [`Property access: ${fullChain}`],
    };
  }

  /**
   * Extract relationship from database call
   */
  private extractFromDatabaseCall(
    awaitExpr: Node,
    handlerName: string
  ): DetectedRelationship | null {
    if (!Node.isAwaitExpression(awaitExpr)) {
      return null;
    }

    const innerExpr = awaitExpr.getExpression();
    if (!Node.isCallExpression(innerExpr)) {
      return null;
    }

    const callExpr = innerExpr.getExpression().getText();

    // Detect database patterns
    if (
      callExpr.includes("db.query") ||
      callExpr.includes("db.execute") ||
      callExpr.includes("db.select") ||
      callExpr.includes("db.insert") ||
      callExpr.includes("db.update") ||
      callExpr.includes("db.delete")
    ) {
      const operation = this.inferDatabaseOperation(callExpr);

      return {
        from: this.toComponentId(handlerName),
        to: "database",
        description: operation,
        technology: "SQL",
        confidence: "high",
        evidence: [`Database call: ${callExpr}`],
      };
    }

    return null;
  }

  /**
   * Extract relationship from fetch/HTTP call
   */
  private extractFromFetchCall(
    callExpr: CallExpression,
    handlerName: string
  ): DetectedRelationship | null {
    const args = callExpr.getArguments();
    if (args.length === 0 || !args[0]) {
      return null;
    }

    const urlArg = args[0].getText();

    // Try to extract API name from URL
    let apiName = "external_api";
    if (urlArg.includes("openai")) {
      apiName = "openai_api";
    } else if (urlArg.includes("anthropic")) {
      apiName = "anthropic_api";
    }

    return {
      from: this.toComponentId(handlerName),
      to: apiName,
      description: "Calls external API",
      technology: "HTTP/REST",
      confidence: "high",
      evidence: [`fetch() call to: ${urlArg}`],
    };
  }

  /**
   * Infer component name from object.method pattern
   */
  private inferComponentFromCall(objectName: string): string | null {
    const mappings: Record<string, string> = {
      db: "db_client",
      database: "database",
      repos: "repositories",
      repository: "repositories",
      repositories: "repositories",
      cache: "cache",
      storage: "storage",
      ai: "ai_service",
      auth: "auth_service",
      authservice: "auth_service",
      user: "user_service",
      userservice: "user_service",
      logger: "logger",
      queue: "queue_service",
    };

    const normalized = objectName.toLowerCase();
    return mappings[normalized] || null;
  }

  /**
   * Infer component name from function name patterns
   * Detects patterns like getDatabase(), createRepositories(), etc.
   */
  private inferComponentFromFunctionName(functionName: string): string | null {
    const normalized = functionName.toLowerCase();

    // Pattern 1: getXxx() or createXxx()
    if (normalized.startsWith("get") || normalized.startsWith("create")) {
      const prefixLength = normalized.startsWith("get") ? 3 : 6;
      const suffix = functionName.substring(prefixLength);
      return this.matchComponentPattern(suffix);
    }

    // Pattern 2: initXxx() or setupXxx()
    if (normalized.startsWith("init") || normalized.startsWith("setup")) {
      const prefixLength = normalized.startsWith("init") ? 4 : 5;
      const suffix = functionName.substring(prefixLength);
      return this.matchInitPattern(suffix);
    }

    return null;
  }

  /**
   * Match component patterns for get/create functions
   */
  private matchComponentPattern(suffix: string): string | null {
    const suffixLower = suffix.toLowerCase();

    const componentPatterns = [
      {
        patterns: ["database", "db", "dbconnection", "connection"],
        component: "db_client",
      },
      {
        patterns: ["repositories", "repos", "repository"],
        component: "repositories",
      },
      {
        patterns: ["cache"],
        component: "cache",
      },
      {
        patterns: ["storage"],
        component: "storage",
      },
      {
        patterns: ["ai", "llm"],
        component: "ai_service",
      },
      {
        patterns: ["logger"],
        component: "logger",
      },
    ];

    for (const { patterns, component } of componentPatterns) {
      if (patterns.some((pattern) => suffixLower.includes(pattern) || suffixLower === pattern)) {
        return component;
      }
    }

    // Service patterns (special case with extraction)
    if (suffixLower.includes("service")) {
      const serviceMatch = suffix.match(/^(.+?)Service/i);
      if (serviceMatch) {
        return this.toComponentId(`${serviceMatch[1]}_service`);
      }
      return "service";
    }

    return null;
  }

  /**
   * Match patterns for init/setup functions
   */
  private matchInitPattern(suffix: string): string | null {
    const suffixLower = suffix.toLowerCase();

    if (suffixLower.includes("database") || suffixLower === "db") {
      return "db_client";
    }
    if (suffixLower.includes("cache")) {
      return "cache";
    }

    return null;
  }

  /**
   * Resolve component from import statement
   */
  private resolveComponentFromImport(functionName: string, sourceFile: SourceFile): string | null {
    for (const importDecl of sourceFile.getImportDeclarations()) {
      const namedImports = importDecl.getNamedImports();

      for (const namedImport of namedImports) {
        if (namedImport.getName() === functionName) {
          const modulePath = importDecl.getModuleSpecifierValue();
          const component = this.inferComponentFromModulePath(modulePath);
          if (component) return component;
        }
      }
    }

    return null;
  }

  /**
   * Infer component from module path
   */
  private inferComponentFromModulePath(modulePath: string): string | null {
    if (modulePath.includes("/db/") || modulePath.includes("/database/")) {
      return "db_client";
    }
    if (modulePath.includes("/repos") || modulePath.includes("/repositories")) {
      return "repositories";
    }
    if (modulePath.includes("/service") || modulePath.includes("/services")) {
      const match = modulePath.match(/\/([^/]+)\.ts$/);
      if (match?.[1]) {
        return this.toComponentId(match[1]);
      }
    }
    return null;
  }

  /**
   * Resolve imported function to its declaration in another file
   * This enables cross-file relationship detection for architectures where
   * handlers are separated from routing logic
   */
  private resolveImportedFunction(
    functionName: string,
    sourceFile: SourceFile
  ): {
    functionDecl: FunctionDeclaration | ArrowFunction | FunctionExpression;
    sourceFile: SourceFile;
  } | null {
    try {
      for (const importDecl of sourceFile.getImportDeclarations()) {
        const namedImports = importDecl.getNamedImports();

        for (const namedImport of namedImports) {
          if (namedImport.getName() === functionName) {
            const moduleSpecifier = importDecl.getModuleSpecifierSourceFile();
            if (!moduleSpecifier) continue;

            const result = this.findFunctionInModule(functionName, moduleSpecifier);
            if (result) return result;
          }
        }
      }
    } catch (_error) {
      // Silently fail on resolution errors (e.g., missing files, parse errors)
      // This ensures the extractor is resilient to incomplete projects
      return null;
    }

    return null;
  }

  /**
   * Find function declaration or arrow function in a module
   */
  private findFunctionInModule(
    functionName: string,
    moduleSpecifier: SourceFile
  ): {
    functionDecl: FunctionDeclaration | ArrowFunction | FunctionExpression;
    sourceFile: SourceFile;
  } | null {
    // Find the function in the imported file
    const functionDecl = moduleSpecifier.getFunction(functionName);
    if (functionDecl) {
      return {
        functionDecl,
        sourceFile: moduleSpecifier,
      };
    }

    // Also check for exported arrow functions or const declarations
    const variableDecl = moduleSpecifier.getVariableDeclaration(functionName);
    if (variableDecl) {
      const initializer = variableDecl.getInitializer();
      if (
        initializer &&
        (Node.isArrowFunction(initializer) || Node.isFunctionExpression(initializer))
      ) {
        return {
          functionDecl: initializer,
          sourceFile: moduleSpecifier,
        };
      }
    }

    return null;
  }

  /**
   * Infer database operation type
   */
  private inferDatabaseOperation(callExpr: string): string {
    if (callExpr.includes("query") || callExpr.includes("select")) {
      return "Reads from database";
    }
    if (
      callExpr.includes("execute") ||
      callExpr.includes("insert") ||
      callExpr.includes("update") ||
      callExpr.includes("delete")
    ) {
      return "Writes to database";
    }
    return "Accesses database";
  }

  /**
   * Convert name to component ID format
   */
  private toComponentId(name: string): string {
    return name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, "_")
      .replace(/^_|_$/g, "");
  }

  /**
   * Remove duplicate relationships
   */
  private deduplicateRelationships(relationships: DetectedRelationship[]): DetectedRelationship[] {
    const seen = new Set<string>();
    const unique: DetectedRelationship[] = [];

    for (const rel of relationships) {
      const key = `${rel.from}->${rel.to}`;
      if (!seen.has(key)) {
        seen.add(key);
        unique.push(rel);
      }
    }

    return unique;
  }
}
