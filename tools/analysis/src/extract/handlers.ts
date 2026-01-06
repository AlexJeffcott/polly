// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations

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
  MessageHandler,
  StateAssignment,
  VerificationCondition,
} from "../types";
import { RelationshipExtractor } from "./relationships";

// State-level constraint extracted from $constraints() calls
export interface StateConstraint {
  field: string;
  messageType: string;
  requires?: string;
  ensures?: string;
  message?: string;
  location: {
    file: string;
    line: number;
  };
}

export interface HandlerAnalysis {
  handlers: MessageHandler[];
  messageTypes: Set<string>;
  stateConstraints: StateConstraint[];
}

export class HandlerExtractor {
  private project: Project;
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>;
  private relationshipExtractor: RelationshipExtractor;
  private analyzedFiles: Set<string>; // Track files we've already analyzed
  private packageRoot: string; // Package directory (contains package.json)

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
    this.typeGuardCache = new WeakMap();
    this.relationshipExtractor = new RelationshipExtractor();
    this.analyzedFiles = new Set<string>();
    // Find package root by looking for package.json from tsconfig location
    this.packageRoot = this.findPackageRoot(tsConfigPath);
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
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = [];
    const messageTypes = new Set<string>();
    const invalidMessageTypes = new Set<string>();
    const stateConstraints: StateConstraint[] = [];

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
        stateConstraints
      );
    }

    this.debugLogExtractionResults(handlers.length, invalidMessageTypes.size);
    this.debugLogAnalysisStats(allSourceFiles.length, entryPoints.length);

    return {
      handlers,
      messageTypes,
      stateConstraints,
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
    stateConstraints: StateConstraint[]
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
          stateConstraints
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
    }
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
    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      this.extractAssignments(handlerArg, assignments);
      this.extractVerificationConditions(handlerArg, preconditions, postconditions);

      // Check for async mutations (potential race conditions)
      this.checkAsyncMutations(handlerArg, messageType);
    }

    const line = callExpr.getStartLineNumber();

    // Extract relationships from handler code
    const sourceFile = callExpr.getSourceFile();
    const handlerName = `${messageType}_handler`;
    let relationships: ComponentRelationship[] | undefined;

    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      const detectedRelationships = this.relationshipExtractor.extractFromHandler(
        handlerArg,
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
    };
  }

  /**
   * Extract state assignments from a handler function
   * Handles:
   * - Simple assignments: state.field = value
   * - Compound operators: state.count += 1
   * - Array mutations: state.items.push(item)
   * - Array indexing: state.items[0] = value
   */
  private extractAssignments(
    funcNode: ArrowFunction | FunctionExpression,
    assignments: StateAssignment[]
  ): void {
    funcNode.forEachDescendant((node: Node) => {
      if (Node.isBinaryExpression(node)) {
        this.extractBinaryExpressionAssignment(node, assignments);
      }

      if (Node.isCallExpression(node)) {
        this.extractArrayMutationAssignment(node, assignments);
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
   * Extract property access assignment (state.field = value)
   */
  private extractPropertyAccessAssignment(
    left: Node,
    right: Node,
    assignments: StateAssignment[]
  ): void {
    if (!Node.isPropertyAccessExpression(left)) return;

    const fieldPath = this.getPropertyPath(left);
    if (fieldPath.startsWith("state.")) {
      const field = fieldPath.substring(6);
      const value = this.extractValue(right);
      if (value !== undefined) {
        assignments.push({ field, value });
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
    if (!fieldPath.startsWith("state.")) return;

    const field = fieldPath.substring(6);
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
   * Extract compound assignments (+=, -=, *=, /=, %=)
   */
  private extractCompoundAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!Node.isBinaryExpression(node)) return;

    const operator = node.getOperatorToken().getText();
    const left = node.getLeft();
    const right = node.getRight();

    if (Node.isPropertyAccessExpression(left)) {
      const fieldPath = this.getPropertyPath(left);
      if (fieldPath.startsWith("state.")) {
        const field = fieldPath.substring(6);
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
      if (fieldPath.startsWith("state.")) {
        const field = fieldPath.substring(6);
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
    funcNode: ArrowFunction | FunctionExpression,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    const body = funcNode.getBody();
    const statements = Node.isBlock(body) ? body.getStatements() : [body];

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
      if (!this.isHandlerMapInitializer(initializer, varDecl)) {
        return handlers;
      }

      // Extract handlers from object properties
      const properties = initializer.getProperties();
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
   * Check if initializer is a valid handler map
   */
  private isHandlerMapInitializer(
    initializer: Node | undefined,
    varDecl: VariableDeclaration
  ): initializer is ObjectLiteralExpression {
    if (!initializer || !Node.isObjectLiteralExpression(initializer)) {
      return false;
    }

    // Check if variable name suggests it's a handler map
    const varName = varDecl.getName().toLowerCase();
    return /(handler|listener|callback|event)s?/.test(varName);
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

    const line = prop.getStartLineNumber();
    return {
      messageType,
      node: context,
      assignments: [],
      preconditions: [],
      postconditions: [],
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

      if (!Node.isCallExpression(condition)) {
        return null;
      }

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
    } catch (_error) {
      return null;
    }
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

    if (fieldPath.startsWith("state.")) {
      const field = fieldPath.substring(6);
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
    if (!fieldPath.startsWith("state.")) return;

    if (["push", "pop", "shift", "unshift", "splice"].includes(methodName)) {
      const field = fieldPath.substring(6);
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
}

export function extractHandlers(tsConfigPath: string): HandlerAnalysis {
  const extractor = new HandlerExtractor(tsConfigPath);
  return extractor.extractHandlers();
}
