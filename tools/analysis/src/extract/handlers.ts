// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations

import {
  type ArrowFunction,
  type CallExpression,
  type FunctionExpression,
  type Identifier,
  type IfStatement,
  Node,
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

export interface HandlerAnalysis {
  handlers: MessageHandler[];
  messageTypes: Set<string>;
}

export class HandlerExtractor {
  private project: Project;
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>;
  private relationshipExtractor: RelationshipExtractor;

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
    this.typeGuardCache = new WeakMap();
    this.relationshipExtractor = new RelationshipExtractor();
  }

  /**
   * Extract all message handlers from the codebase
   */
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = [];
    const messageTypes = new Set<string>();
    const invalidMessageTypes = new Set<string>();

    // Find all source files
    const sourceFiles = this.project.getSourceFiles();
    this.debugLogSourceFiles(sourceFiles);

    for (const sourceFile of sourceFiles) {
      const fileHandlers = this.extractFromFile(sourceFile);
      handlers.push(...fileHandlers);
      this.categorizeHandlerMessageTypes(fileHandlers, messageTypes, invalidMessageTypes);
    }

    this.debugLogExtractionResults(handlers.length, invalidMessageTypes.size);

    return {
      handlers,
      messageTypes,
    };
  }

  private debugLogSourceFiles(sourceFiles: SourceFile[]): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] Loaded ${sourceFiles.length} source files`);
    if (sourceFiles.length <= 20) {
      for (const sf of sourceFiles) {
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

    // Determine context from file path
    const context = this.inferContext(filePath);

    // Find all handler patterns
    sourceFile.forEachDescendant((node) => {
      if (Node.isCallExpression(node)) {
        const expression = node.getExpression();

        // Pattern 1: .on() calls (bus.on, ws.on, socket.on, etc.)
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

      // Pattern 2: Switch/case message routers
      if (Node.isSwitchStatement(node)) {
        const switchHandlers = this.extractSwitchCaseHandlers(node, context, filePath);
        handlers.push(...switchHandlers);
      }

      // Pattern 3: Handler map patterns (const handlers = { 'EVENT': fn })
      if (Node.isVariableDeclaration(node)) {
        const mapHandlers = this.extractHandlerMapPattern(node, context, filePath);
        handlers.push(...mapHandlers);
      }

      // Pattern 4: Type guard if/else-if chains
      // Only process root if statements, not else-if statements (they're handled by the chain walker)
      if (Node.isIfStatement(node)) {
        const parent = node.getParent();
        const isElseIf = parent && Node.isIfStatement(parent);

        if (!isElseIf) {
          const typeGuardHandlers = this.extractTypeGuardHandlers(node, context, filePath);
          handlers.push(...typeGuardHandlers);
        }
      }
    });

    return handlers;
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
      // Pattern 1: Assignment expressions (state.field = value, state.count += 1)
      if (Node.isBinaryExpression(node)) {
        const operator = node.getOperatorToken().getText();

        // Simple assignment: state.field = value
        if (operator === "=") {
          const left = node.getLeft();
          const right = node.getRight();

          // Check if left side is a state property access
          if (Node.isPropertyAccessExpression(left)) {
            const fieldPath = this.getPropertyPath(left);

            // Check if this is a state access
            if (fieldPath.startsWith("state.")) {
              const field = fieldPath.substring(6); // Remove "state." prefix
              const value = this.extractValue(right);

              if (value !== undefined) {
                assignments.push({
                  field,
                  value,
                });
              }
            }
          }
          // Check if left side is array indexing: state.items[index]
          else if (Node.isElementAccessExpression(left)) {
            const expr = left.getExpression();
            if (Node.isPropertyAccessExpression(expr)) {
              const fieldPath = this.getPropertyPath(expr);
              if (fieldPath.startsWith("state.")) {
                const field = fieldPath.substring(6);
                const indexExpr = left.getArgumentExpression();
                const index = indexExpr ? indexExpr.getText() : "0";
                const value = this.extractValue(right);

                if (value !== undefined) {
                  // Store as TLA+ array update: [field[index+1] = value]
                  // Note: TLA+ uses 1-based indexing
                  const tlaIndex = this.isNumericLiteral(index)
                    ? (Number.parseInt(index) + 1).toString()
                    : `${index} + 1`;

                  assignments.push({
                    field: `${field}[${tlaIndex}]`,
                    value,
                  });
                }
              }
            }
          }
        }
        // Compound assignment operators: +=, -=, *=, /=, %=
        else if (["+=", " -=", "*=", "/=", "%="].includes(operator)) {
          const left = node.getLeft();
          const right = node.getRight();

          if (Node.isPropertyAccessExpression(left)) {
            const fieldPath = this.getPropertyPath(left);

            if (fieldPath.startsWith("state.")) {
              const field = fieldPath.substring(6);
              const rightValue = right.getText();

              // Map compound operator to TLA+ binary operator
              const tlaOp = operator.slice(0, -1); // Remove '=' suffix

              // Store as TLA+ expression: @ + value, @ - value, etc.
              assignments.push({
                field,
                value: `@ ${tlaOp} ${rightValue}`,
              });
            }
          }
        }
      }

      // Pattern 2: Array mutation methods (state.items.push(item), etc.)
      if (Node.isCallExpression(node)) {
        const expr = node.getExpression();

        if (Node.isPropertyAccessExpression(expr)) {
          const methodName = expr.getName();
          const object = expr.getExpression();

          // Check if calling method on state property
          if (Node.isPropertyAccessExpression(object)) {
            const fieldPath = this.getPropertyPath(object);

            if (fieldPath.startsWith("state.")) {
              const field = fieldPath.substring(6);
              const args = node.getArguments().map((arg) => arg.getText());

              // Translate array mutation methods to TLA+ operators
              let tlaValue: string | null = null;

              switch (methodName) {
                case "push":
                  // state.items.push(item) → Append(@, item)
                  if (args.length === 1) {
                    tlaValue = `Append(@, ${args[0]})`;
                  }
                  break;

                case "pop":
                  // state.items.pop() → SubSeq(@, 1, Len(@)-1)
                  tlaValue = "SubSeq(@, 1, Len(@)-1)";
                  break;

                case "shift":
                  // state.items.shift() → Tail(@) or SubSeq(@, 2, Len(@))
                  tlaValue = "Tail(@)";
                  break;

                case "unshift":
                  // state.items.unshift(item) → <<item>> \\o @
                  if (args.length === 1) {
                    tlaValue = `<<${args[0]}>> \\o @`;
                  }
                  break;

                case "splice":
                  // Complex operation - warn about limited support
                  // For now, we don't translate splice
                  if (process.env["POLLY_DEBUG"]) {
                    console.log(
                      `[DEBUG] Warning: splice() mutation on ${fieldPath} not fully translated`
                    );
                  }
                  break;

                default:
                  // Unknown method - skip
                  break;
              }

              if (tlaValue) {
                assignments.push({
                  field,
                  value: tlaValue,
                });
              }
            }
          }
        }
      }
    });
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

    // Get position of first await
    const firstAwaitPos = awaitExpressions[0].getStart();

    // Track mutations and whether they occur after await
    funcNode.forEachDescendant((node: Node) => {
      // Check for state assignments
      if (Node.isBinaryExpression(node)) {
        const operator = node.getOperatorToken().getText();

        if (operator === "=" || ["+=", " -=", "*=", "/=", "%="].includes(operator)) {
          const left = node.getLeft();

          if (Node.isPropertyAccessExpression(left) || Node.isElementAccessExpression(left)) {
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
        }
      }

      // Check for array mutation methods
      if (Node.isCallExpression(node)) {
        const expr = node.getExpression();

        if (Node.isPropertyAccessExpression(expr)) {
          const methodName = expr.getName();
          const object = expr.getExpression();

          if (Node.isPropertyAccessExpression(object)) {
            const fieldPath = this.getPropertyPath(object);

            if (fieldPath.startsWith("state.")) {
              if (["push", "pop", "shift", "unshift", "splice"].includes(methodName)) {
                const field = fieldPath.substring(6);
                const line = node.getStartLineNumber();
                const afterAwait = node.getStart() > firstAwaitPos;

                mutations.push({ field, line, afterAwait });
              }
            }
          }
        }
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

    // Get all statements in the function body
    const statements = Node.isBlock(body) ? body.getStatements() : [body];

    for (const statement of statements) {
      // Look for expression statements that are function calls
      if (Node.isExpressionStatement(statement)) {
        const expr = statement.getExpression();

        if (Node.isCallExpression(expr)) {
          const callee = expr.getExpression();

          if (Node.isIdentifier(callee)) {
            const functionName = callee.getText();

            if (functionName === "requires") {
              // Extract precondition
              const condition = this.extractCondition(expr);
              if (condition) {
                preconditions.push(condition);
              }
            } else if (functionName === "ensures") {
              // Extract postcondition
              const condition = this.extractCondition(expr);
              if (condition) {
                postconditions.push(condition);
              }
            }
          }
        }
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
      if (!initializer || !Node.isObjectLiteralExpression(initializer)) {
        return handlers;
      }

      // Check if variable name suggests it's a handler map
      const varName = varDecl.getName().toLowerCase();
      if (!/(handler|listener|callback|event)s?/.test(varName)) {
        return handlers;
      }

      // Extract handlers from object properties
      const properties = initializer.getProperties();
      for (const prop of properties) {
        if (Node.isPropertyAssignment(prop)) {
          const nameNode = prop.getNameNode();
          let messageType: string | null = null;

          if (Node.isStringLiteral(nameNode)) {
            messageType = nameNode.getLiteralValue();
          } else if (Node.isIdentifier(nameNode)) {
            messageType = nameNode.getText();
          }

          if (messageType) {
            const line = prop.getStartLineNumber();

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
      // Skip malformed object literals
    }

    return handlers;
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
      // Get the source file to find type predicates
      const sourceFile = ifNode.getSourceFile();

      // Use cached type guards or compute if not cached
      let typeGuards = this.typeGuardCache.get(sourceFile);
      if (!typeGuards) {
        typeGuards = this.findTypePredicateFunctions(sourceFile);
        this.typeGuardCache.set(sourceFile, typeGuards);
      }

      // DEBUG: Log local type guards found
      if (process.env["POLLY_DEBUG"]) {
        console.log(`[DEBUG] File: ${sourceFile.getBaseName()}`);
        console.log(`[DEBUG] Local type guards found: ${typeGuards.size}`);
        if (typeGuards.size > 0) {
          for (const [name, type] of typeGuards.entries()) {
            console.log(`[DEBUG]   - ${name} → ${type}`);
          }
        }
      }

      // Don't return early - we still want to try imported type guards
      // even if no local type guards exist

      // Process the if statement and all else-if chains
      let currentIf = ifNode as IfStatement;

      while (currentIf) {
        const handler = this.extractHandlerFromIfClause(currentIf, typeGuards, context, filePath);
        if (handler) {
          handlers.push(handler);

          if (process.env["POLLY_DEBUG"]) {
            console.log(
              `[DEBUG] Found handler: ${handler.messageType} at line ${handler.location.line}`
            );
          }
        }

        // Check for else-if
        const elseStatement = currentIf.getElseStatement();
        if (elseStatement && Node.isIfStatement(elseStatement)) {
          currentIf = elseStatement;
        } else {
          break;
        }
      }
    } catch (error) {
      // DEBUG: Log errors
      if (process.env["POLLY_DEBUG"]) {
        console.log(`[DEBUG] Error in extractTypeGuardHandlers: ${error}`);
      }
    }

    return handlers;
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
      // Cast to IfStatement for type safety
      const ifStmt = ifNode as IfStatement;
      // Get condition expression
      const condition = ifStmt.getExpression();

      // Check if condition is a call expression (function call)
      if (!Node.isCallExpression(condition)) {
        return null;
      }

      // Get the function being called
      const funcExpr = condition.getExpression();
      let funcName: string | undefined;

      if (Node.isIdentifier(funcExpr)) {
        funcName = funcExpr.getText();
      }

      if (process.env["POLLY_DEBUG"] && funcName) {
        console.log(`[DEBUG] Processing if condition with function: ${funcName}`);
      }

      // Try to find message type from local type guards first
      let messageType: string | undefined;

      if (funcName && typeGuards.has(funcName)) {
        // Found in local file
        const guardType = typeGuards.get(funcName);
        if (guardType) {
          messageType = guardType;

          if (process.env["POLLY_DEBUG"]) {
            console.log(`[DEBUG] Found in local type guards: ${funcName} → ${messageType}`);
          }
        }
      } else if (Node.isIdentifier(funcExpr)) {
        // Not found locally - try to resolve from imports
        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] Not found locally, trying import resolution for: ${funcName}`);
        }

        messageType = this.resolveImportedTypeGuard(funcExpr) ?? undefined;
      }

      if (!messageType) {
        if (process.env["POLLY_DEBUG"] && funcName) {
          console.log(`[DEBUG] Could not resolve message type for: ${funcName}`);
        }
        return null;
      }

      // Found a type guard call! Use the message type
      const line = ifStmt.getStartLineNumber();

      // Extract relationships from the if block
      const sourceFile = ifStmt.getSourceFile();
      const handlerName = `${messageType}_handler`;
      let relationships: ComponentRelationship[] | undefined;

      const thenStatement = ifStmt.getThenStatement();
      if (thenStatement) {
        const detectedRelationships = this.relationshipExtractor.extractFromHandler(
          thenStatement,
          sourceFile,
          handlerName
        );
        if (detectedRelationships.length > 0) {
          relationships = detectedRelationships;
        }
      }

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
   * Find all type predicate functions in a source file
   * Returns a map of function name → message type
   * Uses AST-based detection for consistency with imported type guard resolution
   */
  private findTypePredicateFunctions(sourceFile: SourceFile): Map<string, string> {
    const typeGuards = new Map<string, string>();

    sourceFile.forEachDescendant((node) => {
      if (
        Node.isFunctionDeclaration(node) ||
        Node.isFunctionExpression(node) ||
        Node.isArrowFunction(node)
      ) {
        // Check the return type NODE (AST structure) for type predicate
        const returnTypeNode = node.getReturnTypeNode();

        if (returnTypeNode && Node.isTypePredicate(returnTypeNode)) {
          // Extract function name
          let functionName: string | undefined;
          if (Node.isFunctionDeclaration(node)) {
            functionName = node.getName();
          } else if (Node.isFunctionExpression(node)) {
            const parent = node.getParent();
            if (Node.isVariableDeclaration(parent)) {
              functionName = parent.getName();
            }
          } else if (Node.isArrowFunction(node)) {
            const parent = node.getParent();
            if (Node.isVariableDeclaration(parent)) {
              functionName = parent.getName();
            }
          }

          if (functionName) {
            // Extract the type from the type predicate node
            const typeNode = returnTypeNode.getTypeNode();
            let messageType: string | null = null;

            if (typeNode) {
              const typeName = typeNode.getText(); // e.g., "QueryMessage"
              messageType = this.extractMessageTypeFromTypeName(typeName);
            }

            // Fallback: Analyze function body for msg.type === 'value'
            if (!messageType) {
              const body = node.getBody();
              if (body) {
                const bodyText = body.getText();
                const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/);
                if (typeValueMatch) {
                  messageType = typeValueMatch[1] ?? null;
                }
              }
            }

            if (messageType) {
              typeGuards.set(functionName, messageType);
            }
          }
        }
      }
    });

    return typeGuards;
  }

  /**
   * Resolve type guard from imported function
   * Uses ts-morph symbol resolution to find definition across files
   * Checks AST structure, not resolved types (which can lose type predicate info)
   */
  private resolveImportedTypeGuard(identifier: Identifier): string | null {
    try {
      const funcName = identifier.getText();

      // Get the definition nodes (where the function is defined)
      const definitions = identifier.getDefinitionNodes();

      if (definitions.length === 0) {
        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] No definitions found for imported function: ${funcName}`);
        }
        return null;
      }

      for (const def of definitions) {
        // Check if it's a function with type predicate return type
        if (
          Node.isFunctionDeclaration(def) ||
          Node.isFunctionExpression(def) ||
          Node.isArrowFunction(def)
        ) {
          // Check the return type NODE (AST structure), not the resolved TYPE
          // This is critical: ts-morph returns "boolean" for type predicates when checking .getReturnType()
          // but the AST node structure preserves the actual type predicate
          const returnTypeNode = def.getReturnTypeNode();

          if (process.env["POLLY_DEBUG"]) {
            const returnType = def.getReturnType().getText();
            console.log(`[DEBUG] Function ${funcName} return type (resolved): ${returnType}`);
            console.log(`[DEBUG] Has return type node: ${!!returnTypeNode}`);
            console.log(
              `[DEBUG] Is type predicate node: ${returnTypeNode && Node.isTypePredicate(returnTypeNode)}`
            );
          }

          // Check if the return type node is a type predicate
          if (returnTypeNode && Node.isTypePredicate(returnTypeNode)) {
            // Extract the type from the type predicate node
            const typeNode = returnTypeNode.getTypeNode();

            if (typeNode) {
              const typeName = typeNode.getText(); // e.g., "QueryMessage"
              const messageType = this.extractMessageTypeFromTypeName(typeName);

              if (messageType) {
                if (process.env["POLLY_DEBUG"]) {
                  console.log(
                    `[DEBUG] Resolved ${funcName} → ${messageType} (from AST type predicate)`
                  );
                }
                return messageType;
              }
            }
          }

          // Fallback: Analyze function body for msg.type === 'value'
          const body = def.getBody();
          if (body) {
            const bodyText = body.getText();
            const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/);
            if (typeValueMatch) {
              const messageType = typeValueMatch[1] ?? null;

              if (process.env["POLLY_DEBUG"]) {
                console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from body)`);
              }

              return messageType;
            }
          }
        }
      }
    } catch (error) {
      // DEBUG: Log errors
      if (process.env["POLLY_DEBUG"]) {
        console.log(`[DEBUG] Error resolving imported type guard: ${error}`);
      }
    }

    return null;
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

    // Electron contexts (check first as they're more specific)
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

    // PWA/Worker contexts
    if (path.includes("service-worker") || path.includes("sw.ts") || path.includes("sw.js")) {
      return "worker";
    }
    if (path.includes("/worker/") || path.includes("\\worker\\")) {
      return "worker";
    }

    // WebSocket/server app contexts
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

    // Chrome extension contexts
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

    return "unknown";
  }
}

export function extractHandlers(tsConfigPath: string): HandlerAnalysis {
  const extractor = new HandlerExtractor(tsConfigPath);
  return extractor.extractHandlers();
}
