// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations
//
// ═══════════════════════════════════════════════════════════════════════════════
// STATE ASSIGNMENT EXTRACTION - SUPPORTED PATTERNS
// ═══════════════════════════════════════════════════════════════════════════════
//
// The following patterns are extracted and converted to TLA+ state transitions:
//
// OBJECTS:
//   ✓ state.field = value                    → direct assignment
//   ✓ signal.value.field = value             → signal nested field
//   ✓ signal.value = { field: value }        → object literal
//   ✓ signal.value = { ...signal.value, f }  → spread update (extracts changed fields)
//
// ARRAYS:
//   ✓ [...arr, item]                         → Append(@, payload)
//   ✓ [item, ...arr]                         → <<payload>> \o @
//   ✓ arr.filter(...)                        → SelectSeq(@, LAMBDA t: TRUE)
//   ✓ arr.map(...)                           → [i \in DOMAIN @ |-> @[i]]
//   ✓ arr.slice(...)                         → SubSeq(@, 1, Len(@))
//   ✓ arr.concat(...)                        → @ \o <<payload>>
//   ✓ arr.reverse()                          → [i \in DOMAIN @ |-> @[Len(@) - i + 1]]
//
// SETS:
//   ✓ new Set([...set, item])                → @ \union {payload}
//   ✓ new Set([...set].filter(...))          → @ \ {payload}
//   ✓ new Set()                              → {}
//
// MAPS:
//   ✓ new Map([...map, [k, v]])              → [@ EXCEPT ![payload.key] = payload.value]
//   ✓ new Map([...map].filter(...))          → [k \in DOMAIN @ \ {payload.key} |-> @[k]]
//   ✓ new Map()                              → <<>>
//
// ═══════════════════════════════════════════════════════════════════════════════
// UNSUPPORTED PATTERNS (will emit warnings)
// ═══════════════════════════════════════════════════════════════════════════════
//
// MUTATING METHODS (modify in place, don't return new value):
//   ✗ arr.push(), arr.pop(), arr.shift(), arr.unshift(), arr.splice()
//   ✗ arr.sort() with in-place mutation
//   ✗ set.add(), set.delete(), set.clear()
//   ✗ map.set(), map.delete(), map.clear()
//
// QUERY METHODS (return non-collection values):
//   ✗ arr.find(), arr.findIndex(), arr.reduce()
//   ✗ arr.some(), arr.every(), arr.includes(), arr.indexOf()
//   ✗ set.has(), map.has(), map.get()
//
// COMPLEX EXPRESSIONS:
//   ✗ Ternary expressions in assignments
//   ✗ Function calls as values (except supported collection methods)
//   ✗ Computed property names
//   ✗ Dynamic field names
//   ✗ Nested object updates beyond first level
//   ✗ Object.assign(), Object.keys(), Object.values(), Object.entries()
//
// To request support for additional patterns, please open an issue at:
// https://github.com/anthropics/polly/issues
// ═══════════════════════════════════════════════════════════════════════════════

import {
  type ArrowFunction,
  type CallExpression,
  type FunctionDeclaration,
  type FunctionExpression,
  type Identifier,
  type IfStatement,
  Node,
  type ObjectLiteralExpression,
  Project,
  type PropertyAccessExpression,
  type SourceFile,
  type Statement,
  type SwitchStatement,
  SyntaxKind,
  type VariableDeclaration,
} from "ts-morph";
import type {
  ComponentRelationship,
  GlobalStateConstraint,
  MessageHandler,
  StateAssignment,
  StateConstraint,
  VerificationCondition,
  VerifiedStateInfo,
} from "../types";
import { RelationshipExtractor } from "./relationships";

export interface ExtractionWarning {
  type: "unsupported_pattern";
  pattern: string;
  location: string;
  suggestion: string;
}

export interface HandlerAnalysis {
  handlers: MessageHandler[];
  messageTypes: Set<string>;
  stateConstraints: StateConstraint[];
  globalStateConstraints: GlobalStateConstraint[];
  verifiedStates: VerifiedStateInfo[];
  warnings: ExtractionWarning[];
}

export class HandlerExtractor {
  private project: Project;
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>;
  private relationshipExtractor: RelationshipExtractor;
  private analyzedFiles: Set<string>; // Track files we've already analyzed
  private packageRoot: string; // Package directory (contains package.json)
  private warnings: ExtractionWarning[]; // Warnings for unsupported patterns
  private currentFunctionParams: string[] = []; // Current handler's parameter names
  private contextOverrides: Map<string, string>; // path prefix → context name

  constructor(tsConfigPath: string, contextOverrides?: Map<string, string>) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
    this.typeGuardCache = new WeakMap();
    this.relationshipExtractor = new RelationshipExtractor();
    this.analyzedFiles = new Set<string>();
    this.warnings = [];
    this.contextOverrides = contextOverrides || new Map();
    // Find package root by looking for package.json from tsconfig location
    this.packageRoot = this.findPackageRoot(tsConfigPath);
  }

  /**
   * Emit a warning for an unsupported pattern
   */
  private warnUnsupportedPattern(pattern: string, location: string, suggestion: string): void {
    // Deduplicate warnings by pattern + location
    const exists = this.warnings.some((w) => w.pattern === pattern && w.location === location);
    if (!exists) {
      this.warnings.push({
        type: "unsupported_pattern",
        pattern,
        location,
        suggestion,
      });
    }
  }

  /**
   * Extract parameter names from a function
   */
  private extractParameterNames(
    func: ArrowFunction | FunctionExpression | FunctionDeclaration
  ): string[] {
    return func.getParameters().map((p) => p.getName());
  }

  /**
   * Get a location string for a node
   */
  private getNodeLocation(node: Node): string {
    const sourceFile = node.getSourceFile();
    const lineAndCol = sourceFile.getLineAndColumnAtPos(node.getStart());
    const filePath = sourceFile.getFilePath();
    const relativePath = filePath.startsWith(this.packageRoot)
      ? filePath.substring(this.packageRoot.length + 1)
      : filePath;
    return `${relativePath}:${lineAndCol.line}`;
  }

  /**
   * Find the nearest package.json directory from tsconfig location
   * This defines the package boundary - we only analyze files within this package
   */
  private findPackageRoot(tsConfigPath: string): string {
    let dir = tsConfigPath.substring(0, tsConfigPath.lastIndexOf("/"));
    // Walk up until we find package.json
    while (dir.length > 1) {
      try {
        const packageJsonPath = `${dir}/package.json`;
        const file = Bun.file(packageJsonPath);
        if (file.size > 0) {
          // Found package.json
          return dir;
        }
      } catch {
        // Keep looking
      }
      const parentDir = dir.substring(0, dir.lastIndexOf("/"));
      if (parentDir === dir) break; // Reached root
      dir = parentDir;
    }
    // Fallback: use tsconfig directory
    return tsConfigPath.substring(0, tsConfigPath.lastIndexOf("/"));
  }

  /**
   * Extract all message handlers from the codebase
   *
   * Uses transitive import following to discover all reachable code:
   * 1. Start with source files from tsconfig that are within the package
   * 2. Follow imports recursively (within package boundary)
   * 3. Cache analyzed files to avoid re-processing
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Handler extraction requires analyzing multiple patterns and file boundaries
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = [];
    const messageTypes = new Set<string>();
    const invalidMessageTypes = new Set<string>();
    const stateConstraints: StateConstraint[] = [];
    const globalStateConstraints: GlobalStateConstraint[] = [];
    const verifiedStates: VerifiedStateInfo[] = [];
    this.warnings = []; // Clear warnings from previous runs

    // Find all source files from tsconfig as potential entry points
    const allSourceFiles = this.project.getSourceFiles();
    // Filter to only files within the package boundary
    const entryPoints = allSourceFiles.filter((f) => this.isWithinPackage(f.getFilePath()));

    this.debugLogSourceFiles(allSourceFiles, entryPoints);

    // Analyze each entry point and follow its imports transitively
    for (const entryPoint of entryPoints) {
      this.analyzeFileAndImports(
        entryPoint,
        handlers,
        messageTypes,
        invalidMessageTypes,
        stateConstraints,
        globalStateConstraints,
        verifiedStates
      );
    }

    // Issue #27: Second pass - find functions that modify verified states
    if (verifiedStates.length > 0) {
      if (process.env["POLLY_DEBUG"]) {
        console.log(
          `[DEBUG] Found ${verifiedStates.length} verified state(s), scanning for mutating functions...`
        );
      }

      for (const filePath of this.analyzedFiles) {
        const sourceFile = this.project.getSourceFile(filePath);
        if (!sourceFile) continue;

        const mutatingHandlers = this.findStateMutatingFunctions(sourceFile, verifiedStates);

        for (const handler of mutatingHandlers) {
          // Avoid duplicates - check if handler already exists for this message type
          const exists = handlers.some(
            (h) =>
              h.messageType === handler.messageType && h.location.file === handler.location.file
          );

          if (!exists) {
            handlers.push(handler);
            if (this.isValidTLAIdentifier(handler.messageType)) {
              messageTypes.add(handler.messageType);
            } else {
              invalidMessageTypes.add(handler.messageType);
            }
          }
        }
      }
    }

    this.debugLogExtractionResults(handlers.length, invalidMessageTypes.size);
    this.debugLogAnalysisStats(allSourceFiles.length, entryPoints.length);

    return {
      handlers,
      messageTypes,
      stateConstraints,
      globalStateConstraints,
      verifiedStates,
      warnings: this.warnings,
    };
  }

  /**
   * Analyze a file and recursively follow its imports
   *
   * This implements the Knip pattern: follow imports transitively
   * to discover all reachable code, including files outside src/
   * that are imported from analyzed files.
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Import following requires conditional logic for package boundaries, caching, and recursion
  private analyzeFileAndImports(
    sourceFile: SourceFile,
    handlers: MessageHandler[],
    messageTypes: Set<string>,
    invalidMessageTypes: Set<string>,
    stateConstraints: StateConstraint[],
    globalStateConstraints: GlobalStateConstraint[],
    verifiedStates: VerifiedStateInfo[]
  ): void {
    const filePath = sourceFile.getFilePath();

    // Skip if already analyzed
    if (this.analyzedFiles.has(filePath)) {
      return;
    }

    // Mark as analyzed
    this.analyzedFiles.add(filePath);

    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Analyzing: ${filePath}`);
    }

    // Extract handlers from this file
    const fileHandlers = this.extractFromFile(sourceFile);
    handlers.push(...fileHandlers);
    this.categorizeHandlerMessageTypes(fileHandlers, messageTypes, invalidMessageTypes);

    // Extract state constraints from this file
    const fileConstraints = this.extractStateConstraintsFromFile(sourceFile);
    stateConstraints.push(...fileConstraints);

    // Extract global state constraints (stateConstraint() calls)
    const fileGlobalConstraints = this.extractGlobalStateConstraintsFromFile(sourceFile);
    globalStateConstraints.push(...fileGlobalConstraints);

    // Issue #27: Extract verified states from this file
    const fileVerifiedStates = this.extractVerifiedStatesFromFile(sourceFile);
    verifiedStates.push(...fileVerifiedStates);

    // Follow imports to discover more files (within package boundary only)
    const importDeclarations = sourceFile.getImportDeclarations();
    for (const importDecl of importDeclarations) {
      const importedFile = importDecl.getModuleSpecifierSourceFile();

      if (importedFile) {
        const importedPath = importedFile.getFilePath();

        // Only follow imports within the same package
        // This excludes:
        // - node_modules (other packages)
        // - Framework code in monorepo parent (other packages)
        // But includes:
        // - All files in this package (src/, specs/, tests/, etc.)
        if (!this.isWithinPackage(importedPath)) {
          if (process.env["POLLY_DEBUG"]) {
            console.log(`[DEBUG] Skipping external import: ${importedPath}`);
          }
          continue;
        }

        // Recursively analyze imported file
        this.analyzeFileAndImports(
          importedFile,
          handlers,
          messageTypes,
          invalidMessageTypes,
          stateConstraints,
          globalStateConstraints,
          verifiedStates
        );
      } else if (process.env["POLLY_DEBUG"]) {
        // Log unresolved imports for debugging
        const specifier = importDecl.getModuleSpecifierValue();
        if (!specifier.startsWith("node:") && !this.isNodeModuleImport(specifier)) {
          console.log(`[DEBUG] Could not resolve import: ${specifier} in ${filePath}`);
        }
      }
    }
  }

  /**
   * Check if a file path is within the package boundary
   */
  private isWithinPackage(filePath: string): boolean {
    // Must be under package root
    if (!filePath.startsWith(this.packageRoot)) {
      return false;
    }
    // Must not be in node_modules
    if (filePath.includes("/node_modules/")) {
      return false;
    }
    return true;
  }

  /**
   * Check if an import specifier is a node_modules import
   */
  private isNodeModuleImport(specifier: string): boolean {
    // Relative imports start with . or ..
    // Absolute/node_modules imports don't
    return !specifier.startsWith(".") && !specifier.startsWith("/");
  }

  private debugLogAnalysisStats(totalSourceFiles: number, entryPointCount: number): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] Analysis Statistics:`);
    console.log(`[DEBUG]   Package root: ${this.packageRoot}`);
    console.log(`[DEBUG]   Source files from tsconfig: ${totalSourceFiles}`);
    console.log(`[DEBUG]   Entry points (in package): ${entryPointCount}`);
    console.log(`[DEBUG]   Files analyzed (including imports): ${this.analyzedFiles.size}`);
    console.log(
      `[DEBUG]   Additional files discovered: ${this.analyzedFiles.size - entryPointCount}`
    );
  }

  private debugLogSourceFiles(allSourceFiles: SourceFile[], entryPoints: SourceFile[]): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] Loaded ${allSourceFiles.length} source files from tsconfig`);
    console.log(`[DEBUG] Filtered to ${entryPoints.length} entry points within package`);
    if (entryPoints.length <= 20) {
      for (const sf of entryPoints) {
        console.log(`[DEBUG]   - ${sf.getFilePath()}`);
      }
    }
  }

  private categorizeHandlerMessageTypes(
    handlers: MessageHandler[],
    messageTypes: Set<string>,
    invalidMessageTypes: Set<string>
  ): void {
    for (const handler of handlers) {
      if (this.isValidTLAIdentifier(handler.messageType)) {
        messageTypes.add(handler.messageType);
      } else {
        invalidMessageTypes.add(handler.messageType);
      }
    }
  }

  private debugLogExtractionResults(handlerCount: number, invalidCount: number): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] Total handlers extracted: ${handlerCount}`);
    if (invalidCount > 0) {
      console.log(`[DEBUG] Filtered ${invalidCount} invalid message type(s) from handlers`);
    }
  }

  /**
   * Check if a string is a valid TLA+ identifier
   * TLA+ identifiers must:
   * - Start with a letter (a-zA-Z)
   * - Contain only letters, digits, and underscores
   * - Not be empty
   */
  private isValidTLAIdentifier(s: string): boolean {
    if (!s || s.length === 0) {
      return false;
    }
    // TLA+ identifiers: start with letter, contain only alphanumeric + underscore
    return /^[a-zA-Z][a-zA-Z0-9_]*$/.test(s);
  }

  /**
   * Extract handlers from a single source file
   */
  private extractFromFile(sourceFile: SourceFile): MessageHandler[] {
    const handlers: MessageHandler[] = [];
    const filePath = sourceFile.getFilePath();
    const context = this.inferContext(filePath);

    sourceFile.forEachDescendant((node) => {
      this.processNodeForHandlers(node, context, filePath, handlers);
    });

    return handlers;
  }

  /**
   * Process a single node to find handler patterns
   */
  private processNodeForHandlers(
    node: Node,
    context: string,
    filePath: string,
    handlers: MessageHandler[]
  ): void {
    if (Node.isCallExpression(node)) {
      this.processCallExpressionHandler(node, context, filePath, handlers);
    }

    if (Node.isSwitchStatement(node)) {
      const switchHandlers = this.extractSwitchCaseHandlers(node, context, filePath);
      handlers.push(...switchHandlers);
    }

    if (Node.isVariableDeclaration(node)) {
      const mapHandlers = this.extractHandlerMapPattern(node, context, filePath);
      handlers.push(...mapHandlers);
    }

    if (Node.isIfStatement(node) && !this.isElseIfStatement(node)) {
      const typeGuardHandlers = this.extractTypeGuardHandlers(node, context, filePath);
      handlers.push(...typeGuardHandlers);
    }
  }

  /**
   * Process call expression to find .on() or .addEventListener() handlers
   */
  private processCallExpressionHandler(
    node: CallExpression,
    context: string,
    filePath: string,
    handlers: MessageHandler[]
  ): void {
    const expression = node.getExpression();

    if (Node.isPropertyAccessExpression(expression)) {
      const methodName = expression.getName();

      if (methodName === "on" || methodName === "addEventListener") {
        const handler = this.extractHandler(node, context, filePath);
        if (handler) {
          handlers.push(handler);
        }
      }

      if (methodName === "ws") {
        this.extractElysiaWsHandlers(node, context, filePath, handlers);
      }

      // REST route handlers
      if (this.isRestMethod(methodName) && this.isWebFrameworkFile(node.getSourceFile())) {
        const restHandler = this.extractRestHandler(node, methodName, context, filePath);
        if (restHandler) {
          handlers.push(restHandler);
        }
      }
    }
  }

  /**
   * Check if a method name is a REST HTTP method
   */
  private isRestMethod(name: string): boolean {
    return ["get", "post", "put", "delete", "patch"].includes(name);
  }

  /**
   * Check if a node is an else-if statement
   */
  private isElseIfStatement(node: Node): boolean {
    const parent = node.getParent();
    return parent !== undefined && Node.isIfStatement(parent);
  }

  /**
   * Extract handler details from a .on() call expression
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: handler extraction requires branching logic
  private extractHandler(
    callExpr: CallExpression,
    context: string,
    filePath: string
  ): MessageHandler | null {
    const args = callExpr.getArguments();

    if (args.length < 2) {
      return null;
    }

    // First argument should be the message type (string literal)
    const messageTypeArg = args[0];
    let messageType: string | null = null;

    if (Node.isStringLiteral(messageTypeArg)) {
      messageType = messageTypeArg.getLiteralValue();
    } else if (Node.isTemplateExpression(messageTypeArg)) {
      // Handle template literals if needed
      messageType = messageTypeArg.getText().replace(/[`'"]/g, "");
    }

    if (!messageType) {
      return null;
    }

    // Second argument is the handler function
    const handlerArg = args[1];
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    // Parse the handler function for state assignments and verification conditions
    let actualHandler: ArrowFunction | FunctionExpression | FunctionDeclaration | null = null;

    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      actualHandler = handlerArg;
    } else if (Node.isIdentifier(handlerArg)) {
      // Resolve function reference (e.g., bus.on('query', handleQuery))
      actualHandler = this.resolveFunctionReference(handlerArg);
    }

    let parameters: string[] | undefined;

    if (actualHandler) {
      this.currentFunctionParams = this.extractParameterNames(actualHandler);
      parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.extractAssignments(actualHandler, assignments);
      this.extractVerificationConditions(actualHandler, preconditions, postconditions);

      // Check for async mutations (potential race conditions)
      if (Node.isArrowFunction(actualHandler) || Node.isFunctionExpression(actualHandler)) {
        this.checkAsyncMutations(actualHandler, messageType);
      }
      this.currentFunctionParams = [];
    }

    const line = callExpr.getStartLineNumber();

    // Extract relationships from handler code
    const sourceFile = callExpr.getSourceFile();
    const handlerName = `${messageType}_handler`;
    let relationships: ComponentRelationship[] | undefined;

    if (actualHandler) {
      const detectedRelationships = this.relationshipExtractor.extractFromHandler(
        actualHandler,
        sourceFile,
        handlerName
      );
      if (detectedRelationships.length > 0) {
        relationships = detectedRelationships;
      }
    }

    return {
      messageType,
      node: context, // Renamed from 'context' to 'node' for generalization
      assignments,
      preconditions,
      postconditions,
      location: {
        file: filePath,
        line,
      },
      relationships,
      origin: "event" as const,
      parameters,
    };
  }

  /**
   * Extract handlers from Elysia .ws() call
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: WebSocket handler extraction requires analyzing multiple callback patterns
  private extractElysiaWsHandlers(
    node: CallExpression,
    context: string,
    filePath: string,
    handlers: MessageHandler[]
  ): void {
    const args = node.getArguments();
    if (args.length < 2) return;

    // First arg is the route path (string)
    const routeArg = args[0];
    if (!routeArg || !Node.isStringLiteral(routeArg)) return;
    const routePath = routeArg.getLiteralValue();

    // Second arg is the config object
    const configArg = args[1];
    if (!configArg || !Node.isObjectLiteralExpression(configArg)) return;

    // Look for message, open, close callbacks
    const callbacks = ["message", "open", "close"];
    for (const cbName of callbacks) {
      const prop = configArg.getProperty(cbName);
      if (!prop) continue;

      let funcBody: ArrowFunction | FunctionExpression | FunctionDeclaration | null = null;

      if (Node.isMethodDeclaration(prop)) {
        // Method shorthand: message(ws, data) { ... }
        // Use the method body directly for analysis
        funcBody = prop as unknown as FunctionDeclaration;
      } else if (Node.isPropertyAssignment(prop)) {
        const init = prop.getInitializer();
        if (init && (Node.isArrowFunction(init) || Node.isFunctionExpression(init))) {
          funcBody = init;
        }
      }

      if (!funcBody) continue;

      if (cbName === "message") {
        // Walk body for type guard handlers and switch statements
        const body = funcBody.getBody();
        if (!body) continue;

        const subHandlers = this.extractSubHandlersFromBody(body, context, filePath);

        if (subHandlers.length > 0) {
          handlers.push(...subHandlers);
        } else {
          // No sub-handlers found, register as a generic ws message handler
          handlers.push(
            this.buildWsHandler(
              `ws_message`,
              routePath,
              context,
              filePath,
              funcBody,
              node.getStartLineNumber()
            )
          );
        }
      } else {
        // open/close lifecycle handlers
        handlers.push(
          this.buildWsHandler(
            `ws_${cbName}`,
            routePath,
            context,
            filePath,
            funcBody,
            node.getStartLineNumber()
          )
        );
      }
    }
  }

  /**
   * Extract sub-handlers (type guards and switch cases) from a function body
   */
  private extractSubHandlersFromBody(
    body: Node,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const subHandlers: MessageHandler[] = [];

    body.forEachDescendant((child) => {
      if (Node.isIfStatement(child) && !this.isElseIfStatement(child)) {
        const typeGuardHandlers = this.extractTypeGuardHandlers(child, context, filePath);
        subHandlers.push(...typeGuardHandlers);
      }
      if (Node.isSwitchStatement(child)) {
        const switchHandlers = this.extractSwitchCaseHandlers(child, context, filePath);
        subHandlers.push(...switchHandlers);
      }
    });

    return subHandlers;
  }

  /**
   * Build a WebSocket handler entry
   */
  private buildWsHandler(
    messageType: string,
    _routePath: string,
    context: string,
    filePath: string,
    funcBody: ArrowFunction | FunctionExpression | FunctionDeclaration,
    line: number
  ): MessageHandler {
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    this.currentFunctionParams = this.extractParameterNames(funcBody);
    this.extractAssignments(funcBody, assignments);
    this.extractVerificationConditions(funcBody, preconditions, postconditions);
    this.currentFunctionParams = [];

    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: { file: filePath, line },
      origin: "event" as const,
    };
  }

  /**
   * Extract a REST route handler (.get/.post/.put/.delete/.patch)
   */
  private extractRestHandler(
    node: CallExpression,
    methodName: string,
    context: string,
    filePath: string
  ): MessageHandler | null {
    const args = node.getArguments();
    if (args.length < 2) return null;

    // First arg must be a string literal route path
    const routeArg = args[0];
    if (!routeArg || !Node.isStringLiteral(routeArg)) return null;
    const routePath = routeArg.getLiteralValue();

    const httpMethod = methodName.toUpperCase();
    const messageType = `${httpMethod} ${routePath}`;

    // Second arg is the handler function
    const handlerArg = args[1];
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    let actualHandler: ArrowFunction | FunctionExpression | FunctionDeclaration | null = null;

    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      actualHandler = handlerArg;
    } else if (Node.isIdentifier(handlerArg)) {
      actualHandler = this.resolveFunctionReference(handlerArg);
    }

    let parameters: string[] | undefined;

    if (actualHandler) {
      this.currentFunctionParams = this.extractParameterNames(actualHandler);
      parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.extractAssignments(actualHandler, assignments);
      this.extractVerificationConditions(actualHandler, preconditions, postconditions);
      this.currentFunctionParams = [];
    }

    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: {
        file: filePath,
        line: node.getStartLineNumber(),
      },
      origin: "event" as const,
      parameters,
      handlerKind: "rest",
      httpMethod,
      routePath,
    };
  }

  /**
   * Check if a source file imports from a known web framework
   */
  private isWebFrameworkFile(sourceFile: SourceFile): boolean {
    const frameworks = ["elysia", "express", "hono", "fastify", "koa", "@elysiajs/eden"];
    for (const importDecl of sourceFile.getImportDeclarations()) {
      const specifier = importDecl.getModuleSpecifierValue();
      if (frameworks.some((fw) => specifier === fw || specifier.startsWith(`${fw}/`))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Extract state assignments from a handler function
   * Handles:
   * - Simple assignments: state.field = value
   * - Compound operators: state.count += 1
   * - Unary operators: state.count++, state.count--, ++state.count, --state.count
   * - Array mutations: state.items.push(item)
   * - Array indexing: state.items[0] = value
   */
  private extractAssignments(
    funcNode: ArrowFunction | FunctionExpression | FunctionDeclaration,
    assignments: StateAssignment[]
  ): void {
    funcNode.forEachDescendant((node: Node) => {
      if (Node.isBinaryExpression(node)) {
        this.extractBinaryExpressionAssignment(node, assignments);
      }

      if (Node.isCallExpression(node)) {
        this.extractArrayMutationAssignment(node, assignments);
      }

      if (Node.isPostfixUnaryExpression(node) || Node.isPrefixUnaryExpression(node)) {
        this.extractUnaryExpressionAssignment(node, assignments);
      }
    });
  }

  /**
   * Extract assignments from binary expressions (=, +=, -=, etc.)
   */
  private extractBinaryExpressionAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isBinaryExpression(node)) return;

    const operator = node.getOperatorToken().getText();

    if (operator === "=") {
      this.extractSimpleOrElementAccessAssignment(node, assignments);
    } else if (["+=", "-=", "*=", "/=", "%="].includes(operator)) {
      this.extractCompoundAssignment(node, assignments);
    }
  }

  /**
   * Extract simple or element access assignments (state.field = value or state.items[0] = value)
   */
  private extractSimpleOrElementAccessAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isBinaryExpression(node)) return;

    const left = node.getLeft();
    const right = node.getRight();

    if (Node.isPropertyAccessExpression(left)) {
      this.extractPropertyAccessAssignment(left, right, assignments);
    } else if (Node.isElementAccessExpression(left)) {
      this.extractElementAccessAssignment(left, right, assignments);
    }
  }

  /**
   * Extract property access assignment (state.field = value or someState.value.field = value)
   */
  private extractPropertyAccessAssignment(
    left: Node,
    right: Node,
    assignments: StateAssignment[]
  ): void {
    if (!Node.isPropertyAccessExpression(left)) return;

    const fieldPath = this.getPropertyPath(left);

    // Try each pattern in order
    if (this.tryExtractStateFieldPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalNestedFieldPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalObjectPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalArrayPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalMethodPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSetConstructorPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractMapConstructorPattern(fieldPath, right, assignments)) return;
    this.tryExtractSignalDirectValuePattern(fieldPath, right, assignments);
  }

  /** Pattern 1: state.field = value */
  private tryExtractStateFieldPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.startsWith("state.")) return false;
    const field = fieldPath.substring(6);
    const value = this.extractValue(right);
    if (value !== undefined) {
      assignments.push({ field, value });
    }
    return true;
  }

  /** Pattern 2: someState.value.field = value (signal pattern with nested field) */
  private tryExtractSignalNestedFieldPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    const valueFieldMatch = fieldPath.match(/^([a-zA-Z_][a-zA-Z0-9_]*)\.value\.(.+)$/);
    if (!valueFieldMatch?.[1] || !valueFieldMatch?.[2]) return false;
    const signalName = valueFieldMatch[1];
    const fieldName = valueFieldMatch[2];
    const value = this.extractValue(right);
    if (value !== undefined) {
      assignments.push({ field: `${signalName}_${fieldName}`, value });
    }
    return true;
  }

  /** Pattern 3: someState.value = { object literal } (signal replacement or spread update) */
  private tryExtractSignalObjectPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !Node.isObjectLiteralExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);
    if (this.isSpreadUpdatePattern(right, fieldPath)) {
      this.extractSpreadUpdateAssignments(right, assignments, signalName);
    } else {
      this.extractObjectLiteralAssignments(right, assignments, signalName);
    }
    return true;
  }

  /** Check if object literal is a spread update pattern: { ...existing, field: value } */
  private isSpreadUpdatePattern(
    objectLiteral: import("ts-morph").ObjectLiteralExpression,
    fieldPath: string
  ): boolean {
    const properties = objectLiteral.getProperties();
    if (properties.length === 0) return false;
    const firstProp = properties[0];
    if (!firstProp || !Node.isSpreadAssignment(firstProp)) return false;
    const spreadExpr = firstProp.getExpression();
    if (!spreadExpr) return false;
    return this.getPropertyPath(spreadExpr) === fieldPath;
  }

  /** Pattern 4: someState.value = [...someState.value, item] (array spread) */
  private tryExtractSignalArrayPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !Node.isArrayLiteralExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);
    const arrayAssignment = this.extractArraySpreadOperation(right, fieldPath, signalName);
    if (arrayAssignment) {
      assignments.push(arrayAssignment);
    }
    return true;
  }

  /** Pattern 5: someState.value = someState.value.filter(...) or .map(...) (array methods) */
  private tryExtractSignalMethodPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !Node.isCallExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);

    // Check for and warn about Set/Map direct method calls that mutate
    this.checkForMutatingCollectionMethods(right);

    const methodAssignment = this.extractArrayMethodOperation(right, fieldPath, signalName);
    if (methodAssignment) {
      assignments.push(methodAssignment);
    }
    return true;
  }

  /** Check for mutating Set/Map methods and emit warnings */
  private checkForMutatingCollectionMethods(callExpr: import("ts-morph").CallExpression): void {
    const expression = callExpr.getExpression();
    if (!Node.isPropertyAccessExpression(expression)) return;

    const methodName = expression.getName();
    const sourceExpr = expression.getExpression();

    // Check for Set mutating methods
    const setMethods = ["add", "delete", "clear"];
    if (setMethods.includes(methodName)) {
      // Try to determine if this is a Set operation by checking the source expression
      const sourceText = sourceExpr.getText();
      if (sourceText.includes("Set") || this.looksLikeSetOrMap(sourceExpr, "Set")) {
        this.warnUnsupportedPattern(
          `set.${methodName}()`,
          this.getNodeLocation(callExpr),
          `Set.${methodName}() mutates in place. Use: new Set([...set, item]) for add, new Set([...set].filter(...)) for delete.`
        );
      }
    }

    // Check for Map mutating methods
    const mapMethods = ["set", "delete", "clear"];
    if (mapMethods.includes(methodName)) {
      const sourceText = sourceExpr.getText();
      if (sourceText.includes("Map") || this.looksLikeSetOrMap(sourceExpr, "Map")) {
        this.warnUnsupportedPattern(
          `map.${methodName}()`,
          this.getNodeLocation(callExpr),
          `Map.${methodName}() mutates in place. Use: new Map([...map, [key, value]]) for set, new Map([...map].filter(...)) for delete.`
        );
      }
    }
  }

  /** Heuristic check if an expression might be a Set or Map */
  private looksLikeSetOrMap(expr: Node, collectionType: "Set" | "Map"): boolean {
    const text = expr.getText().toLowerCase();
    return text.includes(collectionType.toLowerCase());
  }

  /** Pattern 6: someState.value = new Set([...someState.value, item]) (Set operations) */
  private tryExtractSetConstructorPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !Node.isNewExpression(right)) return false;
    const constructorExpr = right.getExpression();
    if (!Node.isIdentifier(constructorExpr) || constructorExpr.getText() !== "Set") return false;

    const signalName = fieldPath.slice(0, -6);
    const setAssignment = this.extractSetOperation(right, fieldPath, signalName);
    if (setAssignment) {
      assignments.push(setAssignment);
    }
    return true;
  }

  /** Pattern 7: someState.value = new Map([...someState.value, [key, val]]) (Map operations) */
  private tryExtractMapConstructorPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !Node.isNewExpression(right)) return false;
    const constructorExpr = right.getExpression();
    if (!Node.isIdentifier(constructorExpr) || constructorExpr.getText() !== "Map") return false;

    const signalName = fieldPath.slice(0, -6);
    const mapAssignment = this.extractMapOperation(right, fieldPath, signalName);
    if (mapAssignment) {
      assignments.push(mapAssignment);
    }
    return true;
  }

  /**
   * Pattern 8: someState.value = expression (direct signal value assignment)
   * Matches signal.value = literal or signal.value = payload.xxx
   */
  private tryExtractSignalDirectValuePattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value")) return false;
    const signalName = fieldPath.slice(0, -6);

    // Try extracting a primitive literal
    const literalValue = this.extractValue(right);
    if (literalValue !== undefined) {
      assignments.push({ field: signalName, value: literalValue });
      return true;
    }

    // Try extracting payload.xxx property access
    if (Node.isPropertyAccessExpression(right)) {
      const rightPath = this.getPropertyPath(right);
      const parts = rightPath.split(".");
      if (
        parts.length === 2 &&
        parts[0] !== undefined &&
        parts[1] !== undefined &&
        this.currentFunctionParams.includes(parts[0])
      ) {
        assignments.push({ field: signalName, value: `param:${parts[1]}` });
        return true;
      }
    }

    return false;
  }

  /** Extract Set operations from new Set(...) constructor */
  private extractSetOperation(
    newExpr: import("ts-morph").NewExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const args = newExpr.getArguments();

    // new Set() - clear operation
    if (args.length === 0) {
      return { field: signalName, value: "{}" };
    }

    const firstArg = args[0];
    if (!firstArg) return null;

    // new Set([...set.value, item]) - add operation
    if (Node.isArrayLiteralExpression(firstArg)) {
      return this.extractSetArrayOperation(firstArg, fieldPath, signalName);
    }

    // new Set([...set.value].filter(...)) - delete operation via method chain
    if (Node.isCallExpression(firstArg)) {
      return this.extractSetMethodChainOperation(firstArg, fieldPath, signalName);
    }

    return null;
  }

  /** Extract Set operation from array literal: new Set([...set.value, item]) */
  private extractSetArrayOperation(
    arrayLiteral: import("ts-morph").ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.getElements();
    if (elements.length < 1) return null;

    const firstElement = elements[0];
    const lastElement = elements[elements.length - 1];

    // Check for add: new Set([...set.value, item])
    if (firstElement && Node.isSpreadElement(firstElement)) {
      const spreadExpr = firstElement.getExpression();
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        // Add operation: @ \union {payload}
        return { field: signalName, value: "@ \\union {payload}" };
      }
    }

    // Check for add at beginning: new Set([item, ...set.value])
    if (lastElement && Node.isSpreadElement(lastElement)) {
      const spreadExpr = lastElement.getExpression();
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        return { field: signalName, value: "{payload} \\union @" };
      }
    }

    return null;
  }

  /** Extract Set operation from method chain: new Set([...set.value].filter(...)) */
  private extractSetMethodChainOperation(
    callExpr: import("ts-morph").CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.getExpression();
    if (!Node.isPropertyAccessExpression(expression)) return null;

    const methodName = expression.getName();
    const sourceExpr = expression.getExpression();

    // Check for [...set.value].filter(...) pattern
    if (methodName === "filter" && Node.isArrayLiteralExpression(sourceExpr)) {
      const elements = sourceExpr.getElements();
      if (elements.length === 1) {
        const spreadEl = elements[0];
        if (spreadEl && Node.isSpreadElement(spreadEl)) {
          const spreadExpr = spreadEl.getExpression();
          if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
            // Delete operation: @ \ {payload}
            return { field: signalName, value: "@ \\ {payload}" };
          }
        }
      }
    }

    return null;
  }

  /** Extract Map operations from new Map(...) constructor */
  private extractMapOperation(
    newExpr: import("ts-morph").NewExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const args = newExpr.getArguments();

    // new Map() - clear operation
    if (args.length === 0) {
      return { field: signalName, value: "<<>>" }; // Empty function in TLA+
    }

    const firstArg = args[0];
    if (!firstArg) return null;

    // new Map([...map.value, [key, value]]) - set operation
    if (Node.isArrayLiteralExpression(firstArg)) {
      return this.extractMapArrayOperation(firstArg, fieldPath, signalName);
    }

    // new Map([...map.value].filter(...)) - delete operation via method chain
    if (Node.isCallExpression(firstArg)) {
      return this.extractMapMethodChainOperation(firstArg, fieldPath, signalName);
    }

    return null;
  }

  /** Extract Map operation from array literal: new Map([...map.value, [key, val]]) */
  private extractMapArrayOperation(
    arrayLiteral: import("ts-morph").ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.getElements();
    if (elements.length < 1) return null;

    const firstElement = elements[0];

    // Check for set: new Map([...map.value, [key, value]])
    if (firstElement && Node.isSpreadElement(firstElement)) {
      const spreadExpr = firstElement.getExpression();
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        // Set operation: [@ EXCEPT ![payload.key] = payload.value]
        return { field: signalName, value: "[@ EXCEPT ![payload.key] = payload.value]" };
      }
    }

    return null;
  }

  /** Extract Map operation from method chain: new Map([...map.value].filter(...)) */
  private extractMapMethodChainOperation(
    callExpr: import("ts-morph").CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.getExpression();
    if (!Node.isPropertyAccessExpression(expression)) return null;

    const methodName = expression.getName();
    const sourceExpr = expression.getExpression();

    // Check for [...map.value].filter(...) pattern
    if (methodName === "filter" && Node.isArrayLiteralExpression(sourceExpr)) {
      const elements = sourceExpr.getElements();
      if (elements.length === 1) {
        const spreadEl = elements[0];
        if (spreadEl && Node.isSpreadElement(spreadEl)) {
          const spreadExpr = spreadEl.getExpression();
          if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
            // Delete operation: restrict domain
            return { field: signalName, value: "[k \\in DOMAIN @ \\ {payload.key} |-> @[k]]" };
          }
        }
      }
    }

    return null;
  }

  /**
   * Extract array method operations: arr.filter(...), arr.map(...)
   */
  private extractArrayMethodOperation(
    callExpr: import("ts-morph").CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.getExpression();
    if (!Node.isPropertyAccessExpression(expression)) return null;

    const methodName = expression.getName();
    const sourceExpr = expression.getExpression();
    const sourcePath = this.getPropertyPath(sourceExpr);

    // Check if source matches target (e.g., todos.value = todos.value.filter(...))
    if (sourcePath !== fieldPath) return null;

    switch (methodName) {
      case "filter":
        // Non-deterministic element removal — codegen emits \E newLen
        return { field: signalName, value: "NDET:FILTER" };

      case "map":
        // Non-deterministic single-element modification — codegen emits \E mapIdx, mapVal
        return { field: signalName, value: "NDET:MAP" };

      case "slice":
        // Subsequence is semantically equivalent to filter in the abstract model
        return { field: signalName, value: "NDET:FILTER" };

      case "concat":
        // Concat appends another sequence
        return { field: signalName, value: "@ \\o <<payload>>" };

      case "reverse":
        // Reverse the sequence
        return { field: signalName, value: "[i \\in DOMAIN @ |-> @[Len(@) - i + 1]]" };

      default:
        // Warn about unsupported array methods
        this.warnUnsupportedArrayMethod(methodName, callExpr);
        return null;
    }
  }

  /** Warn about unsupported array methods */
  private warnUnsupportedArrayMethod(methodName: string, node: Node): void {
    const mutatingMethods = [
      "push",
      "pop",
      "shift",
      "unshift",
      "splice",
      "sort",
      "fill",
      "copyWithin",
    ];
    const queryMethods = [
      "find",
      "findIndex",
      "reduce",
      "reduceRight",
      "some",
      "every",
      "includes",
      "indexOf",
      "lastIndexOf",
    ];
    const otherMethods = ["flat", "flatMap", "join", "toString", "toLocaleString"];

    if (mutatingMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' mutates in place. Use spread syntax: [...arr, item] for append, arr.filter() for removal.`
      );
    } else if (queryMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' returns a single value, not a new array. State assignment won't be extracted.`
      );
    } else if (otherMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' is not supported for state extraction. Consider using map/filter instead.`
      );
    }
  }

  /**
   * Extract assignments from spread update pattern: { ...existing, field: value }
   * Only extracts the explicitly set properties, not the spread
   */
  private extractSpreadUpdateAssignments(
    objectLiteral: import("ts-morph").ObjectLiteralExpression,
    assignments: StateAssignment[],
    signalName: string
  ): void {
    for (const prop of objectLiteral.getProperties()) {
      // Skip spread assignments (they preserve existing values)
      if (Node.isSpreadAssignment(prop)) continue;

      // Extract regular property assignments
      this.extractPropertyAssignment(prop, assignments, signalName);
    }
  }

  /**
   * Extract array spread operations: [...arr, item] or [item, ...arr]
   */
  private extractArraySpreadOperation(
    arrayLiteral: import("ts-morph").ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.getElements();
    if (elements.length < 1) return null;

    // Try append pattern first, then prepend
    return (
      this.tryExtractAppendOperation(elements, fieldPath, signalName) ??
      this.tryExtractPrependOperation(elements, fieldPath, signalName)
    );
  }

  /** Extract append operation: [...arr, item] or [...arr, item1, item2] */
  private tryExtractAppendOperation(
    elements: Node[],
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const firstElement = elements[0];
    if (!firstElement || !Node.isSpreadElement(firstElement)) return null;

    const spreadExpr = firstElement.getExpression();
    if (!spreadExpr || this.getPropertyPath(spreadExpr) !== fieldPath) return null;

    if (elements.length === 2) {
      return { field: signalName, value: "Append(@, payload)" };
    }
    const placeholders = Array(elements.length - 1)
      .fill("payload")
      .join(", ");
    return { field: signalName, value: `@ \\o <<${placeholders}>>` };
  }

  /** Extract prepend operation: [item, ...arr] or [item1, item2, ...arr] */
  private tryExtractPrependOperation(
    elements: Node[],
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    if (elements.length < 2) return null;

    const lastElement = elements[elements.length - 1];
    if (!lastElement || !Node.isSpreadElement(lastElement)) return null;

    const spreadExpr = lastElement.getExpression();
    if (!spreadExpr || this.getPropertyPath(spreadExpr) !== fieldPath) return null;

    if (elements.length === 2) {
      return { field: signalName, value: "<<payload>> \\o @" };
    }
    const placeholders = Array(elements.length - 1)
      .fill("payload")
      .join(", ");
    return { field: signalName, value: `<<${placeholders}>> \\o @` };
  }

  /**
   * Extract assignments from object literal properties
   * Used for: someState.value = { field1: value1, field2: value2 }
   * @param signalName - Optional signal name prefix (e.g., "user" for user.value = {...})
   */
  private extractObjectLiteralAssignments(
    objectLiteral: Node,
    assignments: StateAssignment[],
    signalName?: string
  ): void {
    if (!Node.isObjectLiteralExpression(objectLiteral)) return;

    for (const prop of objectLiteral.getProperties()) {
      this.extractPropertyAssignment(prop, assignments, signalName);
    }
  }

  /**
   * Extract a single property assignment from an object literal property
   */
  private extractPropertyAssignment(
    prop: Node,
    assignments: StateAssignment[],
    signalName?: string
  ): void {
    // Handle regular property assignments: { field: value }
    if (Node.isPropertyAssignment(prop)) {
      const name = prop.getName();
      const initializer = prop.getInitializer();
      if (!name || !initializer) return;

      const value = this.extractValue(initializer);
      if (value === undefined) return;

      // Prefix field name with signal name if provided (e.g., user_loggedIn)
      const field = signalName ? `${signalName}_${name}` : name;
      assignments.push({ field, value });
      return;
    }

    // Handle shorthand properties: { field }
    if (Node.isShorthandPropertyAssignment(prop)) {
      const name = prop.getName();
      const field = signalName ? `${signalName}_${name}` : name;
      // If the identifier matches a function parameter, trace it to payload
      if (this.currentFunctionParams.includes(name)) {
        assignments.push({ field, value: `param:${name}` });
      } else {
        // For shorthand, we can't extract the value statically
        // but we know the field is being set
        assignments.push({ field, value: "@" }); // Use @ as placeholder
      }
    }
  }

  /**
   * Extract element access assignment (state.items[index] = value)
   */
  private extractElementAccessAssignment(
    left: Node,
    right: Node,
    assignments: StateAssignment[]
  ): void {
    if (!Node.isElementAccessExpression(left)) return;

    const expr = left.getExpression();
    if (!Node.isPropertyAccessExpression(expr)) return;

    const fieldPath = this.getPropertyPath(expr);
    const field = this.extractFieldFromStatePath(fieldPath);

    if (!field) return;
    const indexExpr = left.getArgumentExpression();
    const index = indexExpr ? indexExpr.getText() : "0";
    const value = this.extractValue(right);

    if (value !== undefined) {
      const tlaIndex = this.isNumericLiteral(index)
        ? (Number.parseInt(index, 10) + 1).toString()
        : `${index} + 1`;
      assignments.push({
        field: `${field}[${tlaIndex}]`,
        value,
      });
    }
  }

  /**
   * Check if field path is a state mutation pattern and extract field name
   * Supports: state.field, someState.value.field
   * Returns: field name or null if not a state pattern
   */
  private extractFieldFromStatePath(fieldPath: string): string | null {
    // Pattern 1: state.field
    if (fieldPath.startsWith("state.")) {
      return fieldPath.substring(6);
    }

    // Pattern 2: someState.value.field
    const valueMatch = fieldPath.match(/\.value\.(.+)$/);
    if (valueMatch?.[1]) {
      return valueMatch[1];
    }

    return null;
  }

  /**
   * Extract compound assignments (+=, -=, *=, /=, %=)
   */
  private extractCompoundAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isBinaryExpression(node)) return;

    const operator = node.getOperatorToken().getText();
    const left = node.getLeft();
    const right = node.getRight();

    if (Node.isPropertyAccessExpression(left)) {
      const fieldPath = this.getPropertyPath(left);
      const field = this.extractFieldFromStatePath(fieldPath);

      if (field) {
        const rightValue = right.getText();
        const tlaOp = operator.slice(0, -1); // Remove '=' suffix
        assignments.push({
          field,
          value: `@ ${tlaOp} ${rightValue}`,
        });
      }
    }
  }

  /**
   * Get operator text from unary expression token
   */
  private getUnaryOperatorText(operator: unknown): string | null {
    if (typeof operator === "number") {
      // It's a SyntaxKind enum value
      if (operator === SyntaxKind.PlusPlusToken) return "++";
      if (operator === SyntaxKind.MinusMinusToken) return "--";
      return null;
    }
    if (operator && typeof operator === "object" && "getText" in operator) {
      // It's a Node with getText method
      return (operator as { getText(): string }).getText();
    }
    return null;
  }

  /**
   * Extract unary expression assignments (++, --)
   */
  private extractUnaryExpressionAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isPostfixUnaryExpression(node) && !Node.isPrefixUnaryExpression(node)) return;

    const operator = node.getOperatorToken();
    const operatorText = this.getUnaryOperatorText(operator);

    // Only handle ++ and --
    if (operatorText !== "++" && operatorText !== "--") return;

    const operand = node.getOperand();
    if (!Node.isPropertyAccessExpression(operand)) return;

    const fieldPath = this.getPropertyPath(operand);
    const field = this.extractFieldFromStatePath(fieldPath);

    if (field) {
      // Translate ++ to @ + 1 and -- to @ - 1
      const value = operatorText === "++" ? "@ + 1" : "@ - 1";
      assignments.push({ field, value });
    }
  }

  /**
   * Extract array mutation assignments (push, pop, shift, unshift, splice)
   */
  private extractArrayMutationAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isCallExpression(node)) return;

    const expr = node.getExpression();
    if (!Node.isPropertyAccessExpression(expr)) return;

    const methodName = expr.getName();
    const object = expr.getExpression();

    if (Node.isPropertyAccessExpression(object)) {
      const fieldPath = this.getPropertyPath(object);
      const field = this.extractFieldFromStatePath(fieldPath);

      if (field) {
        const args = node.getArguments().map((arg) => arg.getText());
        const tlaValue = this.translateArrayMethod(methodName, args, fieldPath);

        if (tlaValue) {
          assignments.push({ field, value: tlaValue });
        }
      }
    }
  }

  /**
   * Translate array mutation methods to TLA+ operators
   */
  private translateArrayMethod(
    methodName: string,
    args: string[],
    fieldPath: string
  ): string | null {
    switch (methodName) {
      case "push":
        return args.length === 1 ? `Append(@, ${args[0]})` : null;

      case "pop":
        return "SubSeq(@, 1, Len(@)-1)";

      case "shift":
        return "Tail(@)";

      case "unshift":
        return args.length === 1 ? `<<${args[0]}>> \\o @` : null;

      case "splice":
        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] Warning: splice() mutation on ${fieldPath} not fully translated`);
        }
        return null;

      default:
        return null;
    }
  }

  /**
   * Check for async mutations that could cause race conditions
   * Warns when async handlers have state mutations after await expressions
   */
  private checkAsyncMutations(
    funcNode: ArrowFunction | FunctionExpression,
    messageType: string
  ): void {
    // Check if function is async
    const isAsync =
      funcNode.hasModifier?.(SyntaxKind.AsyncKeyword) ||
      funcNode.getModifiers?.()?.some((m: Node) => m.getKind() === SyntaxKind.AsyncKeyword);

    if (!isAsync) {
      return; // Not async, no race conditions possible
    }

    // Find all await expressions
    const awaitExpressions: Node[] = [];
    funcNode.forEachDescendant((node: Node) => {
      if (Node.isAwaitExpression(node)) {
        awaitExpressions.push(node);
      }
    });

    if (awaitExpressions.length === 0) {
      return; // No awaits, no interleaving possible
    }

    // Find all state mutations
    const mutations: Array<{ field: string; line: number; afterAwait: boolean }> = [];
    const body = funcNode.getBody();

    if (!body) {
      return;
    }

    const firstAwait = awaitExpressions[0];
    if (!firstAwait) return;

    // Get position of first await
    const firstAwaitPos = firstAwait.getStart();

    // Track mutations and whether they occur after await
    funcNode.forEachDescendant((node: Node) => {
      if (Node.isBinaryExpression(node)) {
        this.checkBinaryExpressionMutation(node, firstAwaitPos, mutations);
      }

      if (Node.isCallExpression(node)) {
        this.checkCallExpressionMutation(node, firstAwaitPos, mutations);
      }
    });

    // Filter to mutations after await
    const mutationsAfterAwait = mutations.filter((m) => m.afterAwait);

    if (mutationsAfterAwait.length > 0 && process.env["POLLY_DEBUG"]) {
      console.log(
        `[DEBUG] Warning: Async handler for '${messageType}' has ${mutationsAfterAwait.length} state mutation(s) after await`
      );
      console.log(
        "[DEBUG]   This may cause race conditions if multiple messages are processed concurrently"
      );
      console.log(
        `[DEBUG]   Mutations: ${mutationsAfterAwait.map((m) => `${m.field} (line ${m.line})`).join(", ")}`
      );
    }
  }

  /**
   * Extract verification conditions (requires/ensures) from a handler function
   */
  private extractVerificationConditions(
    funcNode: ArrowFunction | FunctionExpression | FunctionDeclaration,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    const body = funcNode.getBody();
    const statements = Node.isBlock(body) ? body.getStatements() : body ? [body] : [];

    for (const statement of statements) {
      this.processStatementForConditions(statement, preconditions, postconditions);
    }
  }

  /**
   * Process a statement to extract verification conditions
   */
  private processStatementForConditions(
    statement: Node | Statement,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    if (!Node.isExpressionStatement(statement)) return;

    const expr = statement.getExpression();
    if (!Node.isCallExpression(expr)) return;

    const callee = expr.getExpression();
    if (!Node.isIdentifier(callee)) return;

    const functionName = callee.getText();

    if (functionName === "requires") {
      const condition = this.extractCondition(expr);
      if (condition) {
        preconditions.push(condition);
      }
    } else if (functionName === "ensures") {
      const condition = this.extractCondition(expr);
      if (condition) {
        postconditions.push(condition);
      }
    }
  }

  /**
   * Extract condition from a requires() or ensures() call
   */
  private extractCondition(callExpr: CallExpression): VerificationCondition | null {
    const args = callExpr.getArguments();

    if (args.length === 0) {
      return null;
    }

    // First argument is the condition expression
    const conditionArg = args[0];
    if (!conditionArg) return null;

    const expression = conditionArg.getText();

    // Second argument (optional) is the message
    let message: string | undefined;
    if (args.length >= 2 && Node.isStringLiteral(args[1])) {
      message = args[1].getLiteralValue();
    }

    const line = callExpr.getStartLineNumber();
    const column = callExpr.getStartLinePos();

    return {
      expression,
      message,
      location: {
        line,
        column,
      },
    };
  }

  /**
   * Get the full property access path (e.g., "state.user.loggedIn")
   */
  private getPropertyPath(node: PropertyAccessExpression | Node): string {
    const parts: string[] = [];

    let current = node;
    while (Node.isPropertyAccessExpression(current)) {
      parts.unshift(current.getName());
      current = current.getExpression();
    }

    // Add the base identifier
    if (Node.isIdentifier(current)) {
      parts.unshift(current.getText());
    }

    return parts.join(".");
  }

  /**
   * Extract a literal value from an expression
   */
  private extractValue(node: Node): string | boolean | number | null | undefined {
    if (Node.isStringLiteral(node)) {
      return node.getLiteralValue();
    }

    if (Node.isNumericLiteral(node)) {
      return node.getLiteralValue();
    }

    if (node.getKind() === SyntaxKind.TrueKeyword) {
      return true;
    }

    if (node.getKind() === SyntaxKind.FalseKeyword) {
      return false;
    }

    if (node.getKind() === SyntaxKind.NullKeyword) {
      return null;
    }

    // For complex expressions, return undefined (can't extract)
    return undefined;
  }

  /**
   * Check if a string represents a numeric literal
   */
  private isNumericLiteral(str: string): boolean {
    return /^\d+$/.test(str);
  }

  /**
   * Extract handlers from switch/case message router patterns
   * Detects: switch(message.type) { case 'EVENT': handler(); }
   */
  private extractSwitchCaseHandlers(
    switchNode: SwitchStatement,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = [];

    try {
      // Check if switching on message.type or similar
      const expression = switchNode.getExpression();
      const expressionText = expression.getText();

      // Look for patterns like: message.type, data.type, msg.type, event.type
      if (!/\.(type|kind|event|action)/.test(expressionText)) {
        return handlers;
      }

      // Extract handlers from each case clause
      const caseClauses = switchNode.getClauses();
      for (const clause of caseClauses) {
        if (Node.isCaseClause(clause)) {
          const caseExpr = clause.getExpression();

          // Extract message type from case expression
          let messageType: string | null = null;
          if (Node.isStringLiteral(caseExpr)) {
            messageType = caseExpr.getLiteralValue();
          }

          if (messageType) {
            const line = clause.getStartLineNumber();

            handlers.push({
              messageType,
              node: context,
              assignments: [],
              preconditions: [],
              postconditions: [],
              location: { file: filePath, line },
              origin: "event" as const,
            });
          }
        }
      }
    } catch (_error) {
      // Skip malformed switch statements
    }

    return handlers;
  }

  /**
   * Extract handlers from handler map patterns
   * Detects: const handlers = { 'EVENT': handlerFn, ... }
   */
  private extractHandlerMapPattern(
    varDecl: VariableDeclaration,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = [];

    try {
      const initializer = varDecl.getInitializer();
      if (!initializer) {
        return handlers;
      }

      // Get the object literal - either direct or from defineHandlers() call
      const objectLiteral = this.getHandlerMapObject(initializer, varDecl);
      if (!objectLiteral) {
        return handlers;
      }

      // Extract handlers from object properties
      const properties = objectLiteral.getProperties();
      for (const prop of properties) {
        const handler = this.extractHandlerFromProperty(prop, context, filePath);
        if (handler) {
          handlers.push(handler);
        }
      }
    } catch (_error) {
      // Skip malformed object literals
    }

    return handlers;
  }

  /**
   * Extract the object literal from a handler map.
   * Only processes direct object literals with handler-like variable names.
   */
  private getHandlerMapObject(
    initializer: Node,
    varDecl: VariableDeclaration
  ): ObjectLiteralExpression | null {
    // Only process direct object literals
    if (Node.isObjectLiteralExpression(initializer)) {
      if (this.isHandlerMapName(varDecl.getName())) {
        return initializer;
      }
    }
    return null;
  }

  /**
   * Check if variable name suggests it's a handler map
   */
  private isHandlerMapName(varName: string): boolean {
    return /(handler|listener|callback|event)s?/.test(varName.toLowerCase());
  }

  /**
   * Extract handler from a property assignment in a handler map
   */
  private extractHandlerFromProperty(
    prop: Node,
    context: string,
    filePath: string
  ): MessageHandler | null {
    if (!Node.isPropertyAssignment(prop)) {
      return null;
    }

    const nameNode = prop.getNameNode();
    const messageType = this.getMessageTypeFromPropertyName(nameNode);

    if (!messageType) {
      return null;
    }

    const value = prop.getInitializer();
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    // Extract from the handler function
    if (value) {
      // Case 1: Inline arrow function or function expression
      if (Node.isArrowFunction(value) || Node.isFunctionExpression(value)) {
        this.extractAssignments(value, assignments);
        this.extractVerificationConditions(value, preconditions, postconditions);
      }
      // Case 2: Function reference (e.g., handleQuery)
      else if (Node.isIdentifier(value)) {
        const referencedFunction = this.resolveFunctionReference(value);
        if (referencedFunction) {
          this.extractAssignments(referencedFunction, assignments);
          this.extractVerificationConditions(referencedFunction, preconditions, postconditions);
        }
      }
    }

    const line = prop.getStartLineNumber();
    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: { file: filePath, line },
    };
  }

  /**
   * Extract message type from property name node
   */
  private getMessageTypeFromPropertyName(nameNode: Node): string | null {
    if (Node.isStringLiteral(nameNode)) {
      return nameNode.getLiteralValue();
    }
    if (Node.isIdentifier(nameNode)) {
      return nameNode.getText();
    }
    return null;
  }

  /**
   * Resolve a function reference to its declaration or expression.
   * Handles both named function declarations and variable-assigned functions.
   *
   * @param identifier - The identifier node referencing the function
   * @returns The resolved function node, or null if not found
   */
  private resolveFunctionReference(
    identifier: Node
  ): FunctionDeclaration | ArrowFunction | FunctionExpression | null {
    if (!Node.isIdentifier(identifier)) {
      return null;
    }

    try {
      const definitions = identifier.getDefinitionNodes();

      for (const def of definitions) {
        // Direct function declaration
        if (Node.isFunctionDeclaration(def)) {
          return def;
        }

        // Variable declaration with function initializer
        if (Node.isVariableDeclaration(def)) {
          const initializer = def.getInitializer();
          if (
            initializer &&
            (Node.isArrowFunction(initializer) || Node.isFunctionExpression(initializer))
          ) {
            return initializer;
          }
        }
      }
    } catch (_error) {
      // Failed to resolve - return null
    }

    return null;
  }

  /**
   * Extract handlers from type guard if/else-if patterns
   * Detects: if (isQueryMessage(msg)) { handleQuery(msg); }
   */
  private extractTypeGuardHandlers(
    ifNode: Node,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = [];

    try {
      const sourceFile = ifNode.getSourceFile();
      const typeGuards = this.getOrComputeTypeGuards(sourceFile);

      this.debugLogTypeGuards(sourceFile, typeGuards);
      this.processIfElseChain(ifNode as IfStatement, typeGuards, context, filePath, handlers);
    } catch (error) {
      this.debugLogError(error);
    }

    return handlers;
  }

  /**
   * Get cached type guards or compute if not cached
   */
  private getOrComputeTypeGuards(sourceFile: SourceFile): Map<string, string> {
    let typeGuards = this.typeGuardCache.get(sourceFile);
    if (!typeGuards) {
      typeGuards = this.findTypePredicateFunctions(sourceFile);
      this.typeGuardCache.set(sourceFile, typeGuards);
    }
    return typeGuards;
  }

  /**
   * Debug log type guards found in source file
   */
  private debugLogTypeGuards(sourceFile: SourceFile, typeGuards: Map<string, string>): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] File: ${sourceFile.getBaseName()}`);
    console.log(`[DEBUG] Local type guards found: ${typeGuards.size}`);

    if (typeGuards.size > 0) {
      for (const [name, type] of typeGuards.entries()) {
        console.log(`[DEBUG]   - ${name} → ${type}`);
      }
    }
  }

  /**
   * Process if-else-if chain to extract handlers
   */
  private processIfElseChain(
    currentIf: IfStatement,
    typeGuards: Map<string, string>,
    context: string,
    filePath: string,
    handlers: MessageHandler[]
  ): void {
    let ifStatement = currentIf;
    while (ifStatement) {
      const handler = this.extractHandlerFromIfClause(ifStatement, typeGuards, context, filePath);

      if (handler) {
        handlers.push(handler);
        this.debugLogFoundHandler(handler);
      }

      // Check for else-if
      const elseStatement = ifStatement.getElseStatement();
      if (elseStatement && Node.isIfStatement(elseStatement)) {
        ifStatement = elseStatement;
      } else {
        break;
      }
    }
  }

  /**
   * Debug log found handler
   */
  private debugLogFoundHandler(handler: MessageHandler): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Found handler: ${handler.messageType} at line ${handler.location.line}`);
    }
  }

  /**
   * Debug log error
   */
  private debugLogError(error: unknown): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Error in extractTypeGuardHandlers: ${error}`);
    }
  }

  /**
   * Extract handler from a single if clause
   */
  private extractHandlerFromIfClause(
    ifNode: Node,
    typeGuards: Map<string, string>,
    context: string,
    filePath: string
  ): MessageHandler | null {
    try {
      const ifStmt = ifNode as IfStatement;
      const condition = ifStmt.getExpression();

      // Pattern 1: Type guard function call — if (isSubscribe(msg))
      if (Node.isCallExpression(condition)) {
        const funcExpr = condition.getExpression();
        const funcName = Node.isIdentifier(funcExpr) ? funcExpr.getText() : undefined;

        this.debugLogProcessingFunction(funcName);

        const messageType = this.resolveMessageType(funcExpr, funcName, typeGuards);
        if (!messageType) {
          this.debugLogUnresolvedMessageType(funcName);
          return null;
        }

        const line = ifStmt.getStartLineNumber();
        const relationships = this.extractRelationshipsFromIfBlock(ifStmt, messageType);

        return {
          messageType,
          node: context,
          assignments: [],
          preconditions: [],
          postconditions: [],
          location: { file: filePath, line },
          relationships,
        };
      }

      // Pattern 2: Equality check — if (data.type === 'subscribe')
      if (Node.isBinaryExpression(condition)) {
        const messageType = this.extractMessageTypeFromEqualityCheck(condition);
        if (messageType) {
          const line = ifStmt.getStartLineNumber();
          const relationships = this.extractRelationshipsFromIfBlock(ifStmt, messageType);

          return {
            messageType,
            node: context,
            assignments: [],
            preconditions: [],
            postconditions: [],
            location: { file: filePath, line },
            relationships,
          };
        }
      }

      return null;
    } catch (_error) {
      return null;
    }
  }

  /**
   * Extract message type from equality check: data.type === 'subscribe'
   */
  private extractMessageTypeFromEqualityCheck(
    expr: import("ts-morph").BinaryExpression
  ): string | null {
    const operator = expr.getOperatorToken().getText();
    if (operator !== "===" && operator !== "==") return null;

    const left = expr.getLeft();
    const right = expr.getRight();

    // Check: xxx.type === 'value' or 'value' === xxx.type
    const stringLiteral = Node.isStringLiteral(right)
      ? right
      : Node.isStringLiteral(left)
        ? left
        : null;
    const propAccess = Node.isPropertyAccessExpression(left)
      ? left
      : Node.isPropertyAccessExpression(right)
        ? right
        : null;

    if (!stringLiteral || !propAccess) return null;

    const propName = propAccess.getName();
    if (propName !== "type" && propName !== "kind" && propName !== "action") {
      return null;
    }

    return stringLiteral.getLiteralValue();
  }

  /**
   * Debug log processing function
   */
  private debugLogProcessingFunction(funcName: string | undefined): void {
    if (process.env["POLLY_DEBUG"] && funcName) {
      console.log(`[DEBUG] Processing if condition with function: ${funcName}`);
    }
  }

  /**
   * Debug log unresolved message type
   */
  private debugLogUnresolvedMessageType(funcName: string | undefined): void {
    if (process.env["POLLY_DEBUG"] && funcName) {
      console.log(`[DEBUG] Could not resolve message type for: ${funcName}`);
    }
  }

  /**
   * Resolve message type from function expression
   */
  private resolveMessageType(
    funcExpr: Node,
    funcName: string | undefined,
    typeGuards: Map<string, string>
  ): string | undefined {
    if (funcName && typeGuards.has(funcName)) {
      const guardType = typeGuards.get(funcName);
      if (guardType) {
        this.debugLogFoundInLocalTypeGuards(funcName, guardType);
        return guardType;
      }
    }

    if (Node.isIdentifier(funcExpr)) {
      this.debugLogTryingImportResolution(funcName);
      return this.resolveImportedTypeGuard(funcExpr) ?? undefined;
    }

    return undefined;
  }

  /**
   * Debug log found in local type guards
   */
  private debugLogFoundInLocalTypeGuards(funcName: string, messageType: string): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Found in local type guards: ${funcName} → ${messageType}`);
    }
  }

  /**
   * Debug log trying import resolution
   */
  private debugLogTryingImportResolution(funcName: string | undefined): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Not found locally, trying import resolution for: ${funcName}`);
    }
  }

  /**
   * Extract relationships from if block
   */
  private extractRelationshipsFromIfBlock(
    ifStmt: IfStatement,
    messageType: string
  ): ComponentRelationship[] | undefined {
    const thenStatement = ifStmt.getThenStatement();
    if (!thenStatement) {
      return undefined;
    }

    const sourceFile = ifStmt.getSourceFile();
    const handlerName = `${messageType}_handler`;
    const detectedRelationships = this.relationshipExtractor.extractFromHandler(
      thenStatement,
      sourceFile,
      handlerName
    );

    return detectedRelationships.length > 0 ? detectedRelationships : undefined;
  }

  /**
   * Find all type predicate functions in a source file
   * Returns a map of function name → message type
   * Uses AST-based detection for consistency with imported type guard resolution
   */
  private findTypePredicateFunctions(sourceFile: SourceFile): Map<string, string> {
    const typeGuards = new Map<string, string>();

    sourceFile.forEachDescendant((node) => {
      this.processTypePredicate(node, typeGuards);
    });

    return typeGuards;
  }

  /**
   * Process a node that might be a type predicate function
   */
  private processTypePredicate(node: Node, typeGuards: Map<string, string>): void {
    if (!this.isFunctionNode(node)) {
      return;
    }

    const returnTypeNode = node.getReturnTypeNode();
    if (!returnTypeNode || !Node.isTypePredicate(returnTypeNode)) {
      return;
    }

    const functionName = this.extractFunctionName(node);
    if (!functionName) {
      return;
    }

    const messageType = this.extractMessageTypeFromTypePredicateFunction(node, returnTypeNode);
    if (messageType) {
      typeGuards.set(functionName, messageType);
    }
  }

  /**
   * Extract function name from function node
   */
  private extractFunctionName(
    node: FunctionDeclaration | FunctionExpression | ArrowFunction
  ): string | undefined {
    if (Node.isFunctionDeclaration(node)) {
      return node.getName();
    }

    if (Node.isFunctionExpression(node) || Node.isArrowFunction(node)) {
      return this.extractFunctionNameFromVariable(node);
    }

    return undefined;
  }

  /**
   * Extract function name from variable declaration
   */
  private extractFunctionNameFromVariable(
    node: FunctionExpression | ArrowFunction
  ): string | undefined {
    const parent = node.getParent();
    if (Node.isVariableDeclaration(parent)) {
      return parent.getName();
    }
    return undefined;
  }

  /**
   * Extract message type from type predicate function
   */
  private extractMessageTypeFromTypePredicateFunction(
    node: FunctionDeclaration | FunctionExpression | ArrowFunction,
    returnTypeNode: Node
  ): string | null {
    if (!Node.isTypePredicate(returnTypeNode)) {
      return null;
    }

    // Try to get type node if method exists
    if ("getTypeNode" in returnTypeNode && typeof returnTypeNode.getTypeNode === "function") {
      const typeNode = returnTypeNode.getTypeNode();

      if (typeNode) {
        const typeName = typeNode.getText();
        const messageType = this.extractMessageTypeFromTypeName(typeName);
        if (messageType) {
          return messageType;
        }
      }
    }

    return this.extractMessageTypeFromFunctionBodyText(node);
  }

  /**
   * Extract message type from function body text
   */
  private extractMessageTypeFromFunctionBodyText(
    node: FunctionDeclaration | FunctionExpression | ArrowFunction
  ): string | null {
    const body = node.getBody();
    if (!body) {
      return null;
    }

    const bodyText = body.getText();
    const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/);

    if (typeValueMatch) {
      return typeValueMatch[1] ?? null;
    }

    return null;
  }

  /**
   * Resolve type guard from imported function
   * Uses ts-morph symbol resolution to find definition across files
   * Checks AST structure, not resolved types (which can lose type predicate info)
   */
  private resolveImportedTypeGuard(identifier: Identifier): string | null {
    try {
      const funcName = identifier.getText();
      const definitions = identifier.getDefinitionNodes();

      if (definitions.length === 0) {
        this.debugLogNoDefinitions(funcName);
        return null;
      }

      for (const def of definitions) {
        const messageType = this.tryExtractTypeGuardFromDefinition(def, funcName);
        if (messageType) {
          return messageType;
        }
      }
    } catch (error) {
      this.debugLogResolutionError(error);
    }

    return null;
  }

  /**
   * Try to extract type guard from a single function definition
   */
  private tryExtractTypeGuardFromDefinition(def: Node, funcName: string): string | null {
    if (!this.isFunctionNode(def)) {
      return null;
    }

    const returnTypeNode = def.getReturnTypeNode();
    this.debugLogReturnTypeInfo(funcName, def, returnTypeNode);

    const typePredicateResult = this.extractFromTypePredicate(returnTypeNode, funcName);
    if (typePredicateResult) {
      return typePredicateResult;
    }

    return this.extractFromFunctionBody(def, funcName);
  }

  /**
   * Check if node is a function type
   */
  private isFunctionNode(
    node: Node
  ): node is FunctionDeclaration | FunctionExpression | ArrowFunction {
    return (
      Node.isFunctionDeclaration(node) ||
      Node.isFunctionExpression(node) ||
      Node.isArrowFunction(node)
    );
  }

  /**
   * Extract message type from type predicate node
   */
  private extractFromTypePredicate(
    returnTypeNode: Node | undefined,
    funcName: string
  ): string | null {
    if (!returnTypeNode || !Node.isTypePredicate(returnTypeNode)) {
      return null;
    }

    const typeNode = returnTypeNode.getTypeNode();
    if (!typeNode) {
      return null;
    }

    const typeName = typeNode.getText();
    const messageType = this.extractMessageTypeFromTypeName(typeName);

    if (messageType) {
      this.debugLogTypePredicateResolution(funcName, messageType);
      return messageType;
    }

    return null;
  }

  /**
   * Extract message type from function body
   */
  private extractFromFunctionBody(
    def: FunctionDeclaration | FunctionExpression | ArrowFunction,
    funcName: string
  ): string | null {
    const body = def.getBody();
    if (!body) {
      return null;
    }

    const bodyText = body.getText();
    const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/);

    if (typeValueMatch) {
      const messageType = typeValueMatch[1] ?? null;
      this.debugLogBodyResolution(funcName, messageType);
      return messageType;
    }

    return null;
  }

  /**
   * Debug: Log no definitions found
   */
  private debugLogNoDefinitions(funcName: string): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] No definitions found for imported function: ${funcName}`);
    }
  }

  /**
   * Debug: Log return type info
   */
  private debugLogReturnTypeInfo(
    funcName: string,
    def: FunctionDeclaration | FunctionExpression | ArrowFunction,
    returnTypeNode: Node | undefined
  ): void {
    if (process.env["POLLY_DEBUG"]) {
      const returnType = def.getReturnType().getText();
      console.log(`[DEBUG] Function ${funcName} return type (resolved): ${returnType}`);
      console.log(`[DEBUG] Has return type node: ${!!returnTypeNode}`);
      console.log(
        `[DEBUG] Is type predicate node: ${returnTypeNode && Node.isTypePredicate(returnTypeNode)}`
      );
    }
  }

  /**
   * Debug: Log type predicate resolution
   */
  private debugLogTypePredicateResolution(funcName: string, messageType: string): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from AST type predicate)`);
    }
  }

  /**
   * Debug: Log body resolution
   */
  private debugLogBodyResolution(funcName: string, messageType: string | null): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from body)`);
    }
  }

  /**
   * Debug: Log resolution error
   */
  private debugLogResolutionError(error: unknown): void {
    if (process.env["POLLY_DEBUG"]) {
      console.log(`[DEBUG] Error resolving imported type guard: ${error}`);
    }
  }

  /**
   * Extract message type from TypeScript type name
   * Examples:
   *   QueryMessage → query
   *   CommandMessage → command
   *   SubscribeMessage → subscribe
   */
  private extractMessageTypeFromTypeName(typeName: string): string {
    // Remove common suffixes and convert to lowercase
    const messageType = typeName
      .replace(/Message$/, "")
      .replace(/Event$/, "")
      .replace(/Request$/, "")
      .replace(/Command$/, "")
      .replace(/Query$/, "")
      .toLowerCase();

    return messageType;
  }

  /**
   * Infer the context (background, content, popup, etc.) from file path
   */
  private inferContext(filePath: string): string {
    // Check context overrides first (monorepo workspace packages)
    for (const [pathPrefix, context] of this.contextOverrides.entries()) {
      if (filePath.startsWith(pathPrefix)) return context;
    }

    const path = filePath.toLowerCase();

    // Check contexts in priority order
    return (
      this.inferElectronContext(path) ||
      this.inferWorkerContext(path) ||
      this.inferServerAppContext(path) ||
      this.inferChromeExtensionContext(path) ||
      "unknown"
    );
  }

  /**
   * Infer Electron context (main, renderer, preload)
   */
  private inferElectronContext(path: string): string | null {
    if (
      path.includes("main.ts") ||
      path.includes("main.js") ||
      path.includes("/main/") ||
      path.includes("\\main\\")
    ) {
      return "main";
    }

    if (
      path.includes("/renderer/") ||
      path.includes("\\renderer\\") ||
      path.includes("renderer.ts") ||
      path.includes("renderer.js")
    ) {
      return "renderer";
    }

    if (path.includes("preload.ts") || path.includes("preload.js")) {
      return "preload";
    }

    return null;
  }

  /**
   * Infer Worker/PWA context
   */
  private inferWorkerContext(path: string): string | null {
    if (path.includes("service-worker") || path.includes("sw.ts") || path.includes("sw.js")) {
      return "worker";
    }

    if (path.includes("/worker/") || path.includes("\\worker\\")) {
      return "worker";
    }

    return null;
  }

  /**
   * Infer WebSocket/server app context
   */
  private inferServerAppContext(path: string): string | null {
    if (
      path.includes("/server/") ||
      path.includes("\\server\\") ||
      path.includes("/server.") ||
      path.includes("server.ts") ||
      path.includes("server.js")
    ) {
      return "server";
    }

    if (path.includes("/client/") || path.includes("\\client\\") || path.includes("/client.")) {
      return "client";
    }

    return null;
  }

  /**
   * Infer Chrome extension context
   */
  private inferChromeExtensionContext(path: string): string | null {
    if (path.includes("/background/") || path.includes("\\background\\")) {
      return "background";
    }

    if (path.includes("/content/") || path.includes("\\content\\")) {
      return "content";
    }

    if (path.includes("/popup/") || path.includes("\\popup\\")) {
      return "popup";
    }

    if (path.includes("/devtools/") || path.includes("\\devtools\\")) {
      return "devtools";
    }

    if (path.includes("/options/") || path.includes("\\options\\")) {
      return "options";
    }

    if (path.includes("/offscreen/") || path.includes("\\offscreen\\")) {
      return "offscreen";
    }

    return null;
  }

  /**
   * Check binary expression for state mutations
   */
  private checkBinaryExpressionMutation(
    node: Node,
    firstAwaitPos: number,
    mutations: Array<{ field: string; line: number; afterAwait: boolean }>
  ): void {
    if (!Node.isBinaryExpression(node)) return;

    const operator = node.getOperatorToken().getText();
    if (operator !== "=" && !["+=", "-=", "*=", "/=", "%="].includes(operator)) return;

    const left = node.getLeft();
    if (!Node.isPropertyAccessExpression(left) && !Node.isElementAccessExpression(left)) return;

    const fieldPath = Node.isPropertyAccessExpression(left)
      ? this.getPropertyPath(left)
      : this.getPropertyPath(left.getExpression());

    const field = this.extractFieldFromStatePath(fieldPath);
    if (field) {
      const line = node.getStartLineNumber();
      const afterAwait = node.getStart() > firstAwaitPos;
      mutations.push({ field, line, afterAwait });
    }
  }

  /**
   * Check call expression for array mutation methods
   */
  private checkCallExpressionMutation(
    node: Node,
    firstAwaitPos: number,
    mutations: Array<{ field: string; line: number; afterAwait: boolean }>
  ): void {
    if (!Node.isCallExpression(node)) return;

    const expr = node.getExpression();
    if (!Node.isPropertyAccessExpression(expr)) return;

    const methodName = expr.getName();
    const object = expr.getExpression();

    if (!Node.isPropertyAccessExpression(object)) return;

    const fieldPath = this.getPropertyPath(object);
    const field = this.extractFieldFromStatePath(fieldPath);

    if (field && ["push", "pop", "shift", "unshift", "splice"].includes(methodName)) {
      const line = node.getStartLineNumber();
      const afterAwait = node.getStart() > firstAwaitPos;
      mutations.push({ field, line, afterAwait });
    }
  }

  /**
   * Extract state-level constraints from a source file
   */
  private extractStateConstraintsFromFile(sourceFile: SourceFile): StateConstraint[] {
    const constraints: StateConstraint[] = [];
    const filePath = sourceFile.getFilePath();

    sourceFile.forEachDescendant((node) => {
      const nodeConstraints = this.recognizeStateConstraint(node, filePath);
      constraints.push(...nodeConstraints);
    });

    return constraints;
  }

  /**
   * Extract global state constraints (stateConstraint() calls) from a source file
   */
  private extractGlobalStateConstraintsFromFile(sourceFile: SourceFile): GlobalStateConstraint[] {
    const constraints: GlobalStateConstraint[] = [];
    const filePath = sourceFile.getFilePath();

    sourceFile.forEachDescendant((node) => {
      const constraint = this.recognizeGlobalStateConstraint(node, filePath);
      if (constraint) {
        constraints.push(constraint);
      }
    });

    return constraints;
  }

  /**
   * Recognize a stateConstraint() call and extract the constraint definition
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Parser logic requires nested conditionals
  private recognizeGlobalStateConstraint(
    node: Node,
    filePath: string
  ): GlobalStateConstraint | null {
    if (!Node.isCallExpression(node)) {
      return null;
    }

    const expression = node.getExpression();
    if (!Node.isIdentifier(expression)) {
      return null;
    }

    const functionName = expression.getText();
    if (functionName !== "stateConstraint") {
      return null;
    }

    const args = node.getArguments();
    if (args.length < 2) {
      return null;
    }

    // Arg 0: string literal → name
    const nameArg = args[0];
    if (!Node.isStringLiteral(nameArg)) {
      return null;
    }
    const name = nameArg.getLiteralValue();

    // Arg 1: arrow function → extract body expression
    const predicateArg = args[1];
    if (!Node.isArrowFunction(predicateArg)) {
      return null;
    }

    const body = predicateArg.getBody();
    let expressionText: string;

    if (Node.isBlock(body)) {
      // Block body: find return statement
      const returnStatement = body.getStatements().find((s) => Node.isReturnStatement(s));
      if (!returnStatement || !Node.isReturnStatement(returnStatement)) {
        return null;
      }
      const returnExpr = returnStatement.getExpression();
      if (!returnExpr) {
        return null;
      }
      expressionText = returnExpr.getText();
    } else {
      // Expression body
      expressionText = body.getText();
    }

    // Arg 2 (optional): object literal with message property
    let message: string | undefined;
    if (args.length >= 3) {
      const optionsArg = args[2];
      if (Node.isObjectLiteralExpression(optionsArg)) {
        for (const prop of optionsArg.getProperties()) {
          if (Node.isPropertyAssignment(prop) && prop.getName() === "message") {
            const value = prop.getInitializer();
            if (value && Node.isStringLiteral(value)) {
              message = value.getLiteralValue();
            }
          }
        }
      }
    }

    return {
      name,
      expression: expressionText,
      message,
      location: {
        file: filePath,
        line: node.getStartLineNumber(),
      },
    };
  }

  /**
   * Recognize a $constraints() call and extract constraint definitions
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Parser logic requires nested conditionals
  private recognizeStateConstraint(node: Node, filePath: string): StateConstraint[] {
    if (!Node.isCallExpression(node)) {
      return [];
    }

    const expression = node.getExpression();
    if (!Node.isIdentifier(expression)) {
      return [];
    }

    const functionName = expression.getText();
    if (functionName !== "$constraints") {
      return [];
    }

    // Get arguments: $constraints(field, constraintsObject)
    const args = node.getArguments();
    if (args.length < 2) {
      return [];
    }

    // First argument is the state field name
    const fieldArg = args[0];
    if (!Node.isStringLiteral(fieldArg)) {
      return [];
    }
    const field = fieldArg.getLiteralValue();

    // Second argument is the constraints object
    const constraintsArg = args[1];
    if (!Node.isObjectLiteralExpression(constraintsArg)) {
      return [];
    }

    // Extract each message type constraint
    const results: StateConstraint[] = [];
    for (const property of constraintsArg.getProperties()) {
      if (!Node.isPropertyAssignment(property)) {
        continue;
      }

      const messageType = property.getName();
      const initializer = property.getInitializer();
      if (!initializer || !Node.isObjectLiteralExpression(initializer)) {
        continue;
      }

      // Extract requires, ensures, and message from the constraint object
      let requires: string | undefined;
      let ensures: string | undefined;
      let message: string | undefined;

      for (const constraintProp of initializer.getProperties()) {
        if (!Node.isPropertyAssignment(constraintProp)) {
          continue;
        }

        const propName = constraintProp.getName();
        const propValue = constraintProp.getInitializer();
        if (!propValue) {
          continue;
        }

        if (propName === "requires" && Node.isStringLiteral(propValue)) {
          requires = propValue.getLiteralValue();
        } else if (propName === "ensures" && Node.isStringLiteral(propValue)) {
          ensures = propValue.getLiteralValue();
        } else if (propName === "message" && Node.isStringLiteral(propValue)) {
          message = propValue.getLiteralValue();
        }
      }

      results.push({
        field,
        messageType,
        requires,
        ensures,
        message,
        location: {
          file: filePath,
          line: property.getStartLineNumber(),
        },
      });
    }

    return results;
  }

  // ═══════════════════════════════════════════════════════════════════
  // Verified State Discovery (Issue #27)
  // ═══════════════════════════════════════════════════════════════════

  /**
   * Extract $sharedState declarations with { verify: true } from a source file
   *
   * Finds patterns like:
   *   const authState = $sharedState('auth', initialState, { verify: true })
   *   export const settings = $syncedState('settings', defaults, { verify: true })
   */
  extractVerifiedStatesFromFile(sourceFile: SourceFile): VerifiedStateInfo[] {
    const verifiedStates: VerifiedStateInfo[] = [];
    const filePath = sourceFile.getFilePath();

    sourceFile.forEachDescendant((node) => {
      if (!Node.isCallExpression(node)) return;

      const stateInfo = this.recognizeVerifiedStateCall(node, filePath);
      if (stateInfo) {
        verifiedStates.push(stateInfo);
      }
    });

    return verifiedStates;
  }

  /**
   * Recognize a $sharedState/$syncedState/$persistedState call with verify: true
   */
  private recognizeVerifiedStateCall(node: Node, filePath: string): VerifiedStateInfo | null {
    if (!Node.isCallExpression(node)) return null;

    const expression = node.getExpression();
    if (!Node.isIdentifier(expression)) return null;

    const funcName = expression.getText();
    // Match state primitives that support verification
    if (!["$sharedState", "$syncedState", "$persistedState"].includes(funcName)) {
      return null;
    }

    const args = node.getArguments();
    if (args.length < 2) return null;

    // Check for { verify: true } in options (3rd argument)
    const optionsArg = args[2];
    if (!optionsArg || !this.hasVerifyTrue(optionsArg)) return null;

    // Extract state key (1st argument)
    const keyArg = args[0];
    if (!keyArg || !Node.isStringLiteral(keyArg)) return null;
    const key = keyArg.getLiteralValue();

    // Get variable name from parent declaration
    const variableName = this.getVariableNameFromParent(node) || key;

    // Extract field names from initial value (2nd argument)
    const initialValueArg = args[1];
    const fields = initialValueArg ? this.extractFieldNames(initialValueArg) : [];

    if (process.env["POLLY_DEBUG"]) {
      console.log(
        `[DEBUG] Found verified state: ${variableName} (key: "${key}") with fields: [${fields.join(", ")}]`
      );
    }

    return {
      key,
      variableName,
      filePath,
      line: node.getStartLineNumber(),
      fields,
    };
  }

  /**
   * Check if an options object contains verify: true
   */
  private hasVerifyTrue(optionsNode: Node): boolean {
    if (!Node.isObjectLiteralExpression(optionsNode)) return false;

    for (const prop of optionsNode.getProperties()) {
      if (!Node.isPropertyAssignment(prop)) continue;

      const name = prop.getName();
      if (name !== "verify") continue;

      const initializer = prop.getInitializer();
      if (initializer && initializer.getKind() === SyntaxKind.TrueKeyword) {
        return true;
      }
    }

    return false;
  }

  /**
   * Get variable name from parent VariableDeclaration
   */
  private getVariableNameFromParent(node: Node): string | null {
    const parent = node.getParent();
    if (Node.isVariableDeclaration(parent)) {
      return parent.getName();
    }
    return null;
  }

  /**
   * Extract field names from an initial value expression
   * Handles object literals and identifier references
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Field extraction requires traversing nested object structures
  private extractFieldNames(node: Node): string[] {
    const fields: string[] = [];

    if (Node.isObjectLiteralExpression(node)) {
      for (const prop of node.getProperties()) {
        if (Node.isPropertyAssignment(prop) || Node.isShorthandPropertyAssignment(prop)) {
          fields.push(prop.getName());
        }
      }
    } else if (Node.isIdentifier(node)) {
      // Try to resolve the identifier to its declaration
      const definitions = node.getDefinitionNodes();
      for (const def of definitions) {
        if (Node.isVariableDeclaration(def)) {
          const initializer = def.getInitializer();
          if (initializer && Node.isObjectLiteralExpression(initializer)) {
            return this.extractFieldNames(initializer);
          }
        }
      }
    }

    return fields;
  }

  /**
   * Find exported functions that modify verified state signals
   *
   * Looks for patterns:
   *   - authState.value = { ... }
   *   - authState.value.field = value
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: State mutation detection requires complex AST pattern matching
  findStateMutatingFunctions(
    sourceFile: SourceFile,
    verifiedStates: VerifiedStateInfo[]
  ): MessageHandler[] {
    const handlers: MessageHandler[] = [];
    const stateVarNames = new Set(verifiedStates.map((s) => s.variableName));
    const filePath = sourceFile.getFilePath();
    const context = this.inferContext(filePath);

    // Find all exported functions
    for (const func of sourceFile.getFunctions()) {
      if (!func.isExported()) continue;

      const funcName = func.getName();
      if (!funcName) continue;

      // Check if function modifies any verified state
      this.currentFunctionParams = this.extractParameterNames(func);
      const assignments = this.findStateMutationsInFunction(func, stateVarNames);
      if (assignments.length === 0) {
        this.currentFunctionParams = [];
        continue;
      }

      // Extract requires/ensures
      const preconditions: VerificationCondition[] = [];
      const postconditions: VerificationCondition[] = [];
      this.extractVerificationConditions(func, preconditions, postconditions);

      // Generate message type from function name
      const messageType = this.functionNameToMessageType(funcName);

      const parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.currentFunctionParams = [];

      if (process.env["POLLY_DEBUG"]) {
        console.log(
          `[DEBUG] Found state-mutating function: ${funcName} → ${messageType} ` +
            `(${assignments.length} assignments, ${preconditions.length} preconditions, ${postconditions.length} postconditions)`
        );
      }

      handlers.push({
        messageType,
        node: context,
        assignments,
        preconditions,
        postconditions,
        location: {
          file: filePath,
          line: func.getStartLineNumber(),
        },
        origin: "stateHandler" as const,
        parameters,
      });
    }

    // Also check exported variable declarations with arrow functions
    for (const varStmt of sourceFile.getVariableStatements()) {
      if (!varStmt.isExported()) continue;

      for (const decl of varStmt.getDeclarations()) {
        const initializer = decl.getInitializer();
        if (!initializer) continue;
        if (!Node.isArrowFunction(initializer) && !Node.isFunctionExpression(initializer)) continue;

        const funcName = decl.getName();
        if (!funcName) continue;

        this.currentFunctionParams = this.extractParameterNames(initializer);
        const assignments = this.findStateMutationsInFunction(initializer, stateVarNames);
        if (assignments.length === 0) {
          this.currentFunctionParams = [];
          continue;
        }

        const preconditions: VerificationCondition[] = [];
        const postconditions: VerificationCondition[] = [];
        this.extractVerificationConditions(initializer, preconditions, postconditions);

        const messageType = this.functionNameToMessageType(funcName);

        const arrowParams =
          this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
        this.currentFunctionParams = [];

        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] Found state-mutating arrow function: ${funcName} → ${messageType}`);
        }

        handlers.push({
          messageType,
          node: context,
          assignments,
          preconditions,
          postconditions,
          location: {
            file: filePath,
            line: decl.getStartLineNumber(),
          },
          origin: "stateHandler" as const,
          parameters: arrowParams,
        });
      }
    }

    return handlers;
  }

  /**
   * Find state mutations within a function that target verified state signals
   */
  private findStateMutationsInFunction(
    func: FunctionDeclaration | ArrowFunction | FunctionExpression,
    stateVarNames: Set<string>
  ): StateAssignment[] {
    const mutations: StateAssignment[] = [];

    // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: AST traversal for state mutations requires multiple pattern checks
    func.forEachDescendant((node) => {
      if (!Node.isBinaryExpression(node)) return;

      const operator = node.getOperatorToken().getText();
      if (operator !== "=") return;

      const left = node.getLeft();
      if (!Node.isPropertyAccessExpression(left)) return;

      const path = this.getPropertyPath(left);

      // Check for patterns:
      // 1. authState.value = { ... }  (full replacement)
      // 2. authState.value.field = value  (field update)
      for (const varName of stateVarNames) {
        // Pattern 1: Full state replacement
        // e.g., authState.value = { loggedIn: true } → authState_loggedIn = true
        if (path === `${varName}.value`) {
          const right = node.getRight();
          if (Node.isObjectLiteralExpression(right)) {
            this.extractObjectLiteralAssignments(right, mutations, varName);
          }
          break;
        }

        // Pattern 2: Field update
        // e.g., authState.value.loggedIn = true → authState_loggedIn = true
        const fieldPrefix = `${varName}.value.`;
        if (path.startsWith(fieldPrefix)) {
          const fieldName = path.substring(fieldPrefix.length);
          const value = this.extractValue(node.getRight());
          mutations.push({ field: `${varName}_${fieldName}`, value: value ?? "@" });
          break;
        }
      }
    });

    return mutations;
  }

  /**
   * Convert function name to message type
   * Examples:
   *   handleAuthSuccess → AuthSuccess
   *   handleLogout → Logout
   *   setUserProfile → SetUserProfile
   */
  private functionNameToMessageType(funcName: string): string {
    // Remove common handler prefixes
    let name = funcName
      .replace(/^handle/, "")
      .replace(/^on/, "")
      .replace(/^set/, "Set")
      .replace(/^update/, "Update")
      .replace(/^do/, "");

    // Ensure first letter is uppercase
    if (name.length > 0) {
      name = name.charAt(0).toUpperCase() + name.slice(1);
    }

    return name || funcName;
  }
}

export function extractHandlers(tsConfigPath: string): HandlerAnalysis {
  const extractor = new HandlerExtractor(tsConfigPath);
  return extractor.extractHandlers();
}
