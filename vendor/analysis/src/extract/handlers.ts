// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations

import { Project, type SourceFile, SyntaxKind, Node, type IfStatement } from "ts-morph"
import type { MessageHandler, StateAssignment, VerificationCondition } from "../types"
import { RelationshipExtractor } from "./relationships"

export interface HandlerAnalysis {
  handlers: MessageHandler[]
  messageTypes: Set<string>
}

export class HandlerExtractor {
  private project: Project
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>
  private relationshipExtractor: RelationshipExtractor

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    })
    this.typeGuardCache = new WeakMap()
    this.relationshipExtractor = new RelationshipExtractor()
  }

  /**
   * Extract all message handlers from the codebase
   */
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = []
    const messageTypes = new Set<string>()
    const invalidMessageTypes = new Set<string>()

    // Find all source files
    const sourceFiles = this.project.getSourceFiles()

    if (process.env['POLLY_DEBUG']) {
      console.log(`[DEBUG] Loaded ${sourceFiles.length} source files`)
      if (sourceFiles.length <= 20) {
        // Only log file names if there aren't too many
        for (const sf of sourceFiles) {
          console.log(`[DEBUG]   - ${sf.getFilePath()}`)
        }
      }
    }

    for (const sourceFile of sourceFiles) {
      const fileHandlers = this.extractFromFile(sourceFile)
      handlers.push(...fileHandlers)

      for (const handler of fileHandlers) {
        if (this.isValidTLAIdentifier(handler.messageType)) {
          messageTypes.add(handler.messageType)
        } else {
          invalidMessageTypes.add(handler.messageType)
        }
      }
    }

    if (process.env['POLLY_DEBUG']) {
      console.log(`[DEBUG] Total handlers extracted: ${handlers.length}`)
      if (invalidMessageTypes.size > 0) {
        console.log(`[DEBUG] Filtered ${invalidMessageTypes.size} invalid message type(s) from handlers`)
      }
    }

    return {
      handlers,
      messageTypes,
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
      return false
    }
    // TLA+ identifiers: start with letter, contain only alphanumeric + underscore
    return /^[a-zA-Z][a-zA-Z0-9_]*$/.test(s)
  }

  /**
   * Extract handlers from a single source file
   */
  private extractFromFile(sourceFile: SourceFile): MessageHandler[] {
    const handlers: MessageHandler[] = []
    const filePath = sourceFile.getFilePath()

    // Determine context from file path
    const context = this.inferContext(filePath)

    // Find all handler patterns
    sourceFile.forEachDescendant((node) => {
      if (Node.isCallExpression(node)) {
        const expression = node.getExpression()

        // Pattern 1: .on() calls (bus.on, ws.on, socket.on, etc.)
        if (Node.isPropertyAccessExpression(expression)) {
          const methodName = expression.getName()

          if (methodName === "on" || methodName === "addEventListener") {
            const handler = this.extractHandler(node, context, filePath)
            if (handler) {
              handlers.push(handler)
            }
          }
        }
      }

      // Pattern 2: Switch/case message routers
      if (Node.isSwitchStatement(node)) {
        const switchHandlers = this.extractSwitchCaseHandlers(node, context, filePath)
        handlers.push(...switchHandlers)
      }

      // Pattern 3: Handler map patterns (const handlers = { 'EVENT': fn })
      if (Node.isVariableDeclaration(node)) {
        const mapHandlers = this.extractHandlerMapPattern(node, context, filePath)
        handlers.push(...mapHandlers)
      }

      // Pattern 4: Type guard if/else-if chains
      // Only process root if statements, not else-if statements (they're handled by the chain walker)
      if (Node.isIfStatement(node)) {
        const parent = node.getParent()
        const isElseIf = parent && Node.isIfStatement(parent)

        if (!isElseIf) {
          const typeGuardHandlers = this.extractTypeGuardHandlers(node, context, filePath)
          handlers.push(...typeGuardHandlers)
        }
      }
    })

    return handlers
  }

  /**
   * Extract handler details from a .on() call expression
   */
  private extractHandler(
    callExpr: any,
    context: string,
    filePath: string
  ): MessageHandler | null {
    const args = callExpr.getArguments()

    if (args.length < 2) {
      return null
    }

    // First argument should be the message type (string literal)
    const messageTypeArg = args[0]
    let messageType: string | null = null

    if (Node.isStringLiteral(messageTypeArg)) {
      messageType = messageTypeArg.getLiteralValue()
    } else if (Node.isTemplateExpression(messageTypeArg)) {
      // Handle template literals if needed
      messageType = messageTypeArg.getText().replace(/[`'"]/g, "")
    }

    if (!messageType) {
      return null
    }

    // Second argument is the handler function
    const handlerArg = args[1]
    const assignments: StateAssignment[] = []
    const preconditions: VerificationCondition[] = []
    const postconditions: VerificationCondition[] = []

    // Parse the handler function for state assignments and verification conditions
    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      this.extractAssignments(handlerArg, assignments)
      this.extractVerificationConditions(handlerArg, preconditions, postconditions)
    }

    const line = callExpr.getStartLineNumber()

    // Extract relationships from handler code
    const sourceFile = callExpr.getSourceFile()
    const handlerName = `${messageType}_handler`
    let relationships = undefined

    if (Node.isArrowFunction(handlerArg) || Node.isFunctionExpression(handlerArg)) {
      const detectedRelationships = this.relationshipExtractor.extractFromHandler(
        handlerArg,
        sourceFile,
        handlerName
      )
      if (detectedRelationships.length > 0) {
        relationships = detectedRelationships
      }
    }

    return {
      messageType,
      node: context,  // Renamed from 'context' to 'node' for generalization
      assignments,
      preconditions,
      postconditions,
      location: {
        file: filePath,
        line,
      },
      relationships,
    }
  }

  /**
   * Extract state assignments from a handler function
   */
  private extractAssignments(funcNode: any, assignments: StateAssignment[]): void {
    funcNode.forEachDescendant((node: any) => {
      // Look for assignment expressions: state.field = value
      if (Node.isBinaryExpression(node)) {
        const operator = node.getOperatorToken().getText()

        if (operator === "=") {
          const left = node.getLeft()
          const right = node.getRight()

          // Check if left side is a state property access
          if (Node.isPropertyAccessExpression(left)) {
            const fieldPath = this.getPropertyPath(left)

            // Check if this is a state access
            if (fieldPath.startsWith("state.")) {
              const field = fieldPath.substring(6)  // Remove "state." prefix
              const value = this.extractValue(right)

              if (value !== undefined) {
                assignments.push({
                  field,
                  value,
                })
              }
            }
          }
        }
      }
    })
  }

  /**
   * Extract verification conditions (requires/ensures) from a handler function
   */
  private extractVerificationConditions(
    funcNode: any,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    const body = funcNode.getBody()

    // Get all statements in the function body
    const statements = Node.isBlock(body) ? body.getStatements() : [body]

    statements.forEach((statement: any) => {
      // Look for expression statements that are function calls
      if (Node.isExpressionStatement(statement)) {
        const expr = statement.getExpression()

        if (Node.isCallExpression(expr)) {
          const callee = expr.getExpression()

          if (Node.isIdentifier(callee)) {
            const functionName = callee.getText()

            if (functionName === "requires") {
              // Extract precondition
              const condition = this.extractCondition(expr)
              if (condition) {
                preconditions.push(condition)
              }
            } else if (functionName === "ensures") {
              // Extract postcondition
              const condition = this.extractCondition(expr)
              if (condition) {
                postconditions.push(condition)
              }
            }
          }
        }
      }
    })
  }

  /**
   * Extract condition from a requires() or ensures() call
   */
  private extractCondition(callExpr: any): VerificationCondition | null {
    const args = callExpr.getArguments()

    if (args.length === 0) {
      return null
    }

    // First argument is the condition expression
    const conditionArg = args[0]
    const expression = conditionArg.getText()

    // Second argument (optional) is the message
    let message: string | undefined
    if (args.length >= 2 && Node.isStringLiteral(args[1])) {
      message = args[1].getLiteralValue()
    }

    const line = callExpr.getStartLineNumber()
    const column = callExpr.getStartLinePos()

    return {
      expression,
      message,
      location: {
        line,
        column,
      },
    }
  }

  /**
   * Get the full property access path (e.g., "state.user.loggedIn")
   */
  private getPropertyPath(node: any): string {
    const parts: string[] = []

    let current = node
    while (Node.isPropertyAccessExpression(current)) {
      parts.unshift(current.getName())
      current = current.getExpression()
    }

    // Add the base identifier
    if (Node.isIdentifier(current)) {
      parts.unshift(current.getText())
    }

    return parts.join(".")
  }

  /**
   * Extract a literal value from an expression
   */
  private extractValue(node: any): string | boolean | number | null | undefined {
    if (Node.isStringLiteral(node)) {
      return node.getLiteralValue()
    }

    if (Node.isNumericLiteral(node)) {
      return node.getLiteralValue()
    }

    if (node.getKind() === SyntaxKind.TrueKeyword) {
      return true
    }

    if (node.getKind() === SyntaxKind.FalseKeyword) {
      return false
    }

    if (node.getKind() === SyntaxKind.NullKeyword) {
      return null
    }

    // For complex expressions, return undefined (can't extract)
    return undefined
  }

  /**
   * Extract handlers from switch/case message router patterns
   * Detects: switch(message.type) { case 'EVENT': handler(); }
   */
  private extractSwitchCaseHandlers(
    switchNode: any,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = []

    try {
      // Check if switching on message.type or similar
      const expression = switchNode.getExpression()
      const expressionText = expression.getText()

      // Look for patterns like: message.type, data.type, msg.type, event.type
      if (!/\.(type|kind|event|action)/.test(expressionText)) {
        return handlers
      }

      // Extract handlers from each case clause
      const caseClauses = switchNode.getClauses()
      for (const clause of caseClauses) {
        if (Node.isCaseClause(clause)) {
          const caseExpr = clause.getExpression()

          // Extract message type from case expression
          let messageType: string | null = null
          if (Node.isStringLiteral(caseExpr)) {
            messageType = caseExpr.getLiteralValue()
          }

          if (messageType) {
            const line = clause.getStartLineNumber()

            handlers.push({
              messageType,
              node: context,
              assignments: [],
              preconditions: [],
              postconditions: [],
              location: { file: filePath, line },
            })
          }
        }
      }
    } catch (error) {
      // Skip malformed switch statements
    }

    return handlers
  }

  /**
   * Extract handlers from handler map patterns
   * Detects: const handlers = { 'EVENT': handlerFn, ... }
   */
  private extractHandlerMapPattern(
    varDecl: any,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = []

    try {
      const initializer = varDecl.getInitializer()
      if (!initializer || !Node.isObjectLiteralExpression(initializer)) {
        return handlers
      }

      // Check if variable name suggests it's a handler map
      const varName = varDecl.getName().toLowerCase()
      if (!/(handler|listener|callback|event)s?/.test(varName)) {
        return handlers
      }

      // Extract handlers from object properties
      const properties = initializer.getProperties()
      for (const prop of properties) {
        if (Node.isPropertyAssignment(prop)) {
          const nameNode = prop.getNameNode()
          let messageType: string | null = null

          if (Node.isStringLiteral(nameNode)) {
            messageType = nameNode.getLiteralValue()
          } else if (Node.isIdentifier(nameNode)) {
            messageType = nameNode.getText()
          }

          if (messageType) {
            const line = prop.getStartLineNumber()

            handlers.push({
              messageType,
              node: context,
              assignments: [],
              preconditions: [],
              postconditions: [],
              location: { file: filePath, line },
            })
          }
        }
      }
    } catch (error) {
      // Skip malformed object literals
    }

    return handlers
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
    const handlers: MessageHandler[] = []

    try {
      // Get the source file to find type predicates
      const sourceFile = ifNode.getSourceFile()

      // Use cached type guards or compute if not cached
      let typeGuards = this.typeGuardCache.get(sourceFile)
      if (!typeGuards) {
        typeGuards = this.findTypePredicateFunctions(sourceFile)
        this.typeGuardCache.set(sourceFile, typeGuards)
      }

      // DEBUG: Log local type guards found
      if (process.env['POLLY_DEBUG']) {
        console.log(`[DEBUG] File: ${sourceFile.getBaseName()}`)
        console.log(`[DEBUG] Local type guards found: ${typeGuards.size}`)
        if (typeGuards.size > 0) {
          for (const [name, type] of typeGuards.entries()) {
            console.log(`[DEBUG]   - ${name} → ${type}`)
          }
        }
      }

      // Don't return early - we still want to try imported type guards
      // even if no local type guards exist

      // Process the if statement and all else-if chains
      let currentIf = ifNode as IfStatement

      while (currentIf) {
        const handler = this.extractHandlerFromIfClause(currentIf, typeGuards, context, filePath)
        if (handler) {
          handlers.push(handler)

          if (process.env['POLLY_DEBUG']) {
            console.log(`[DEBUG] Found handler: ${handler.messageType} at line ${handler.location.line}`)
          }
        }

        // Check for else-if
        const elseStatement = currentIf.getElseStatement()
        if (elseStatement && Node.isIfStatement(elseStatement)) {
          currentIf = elseStatement
        } else {
          break
        }
      }
    } catch (error) {
      // DEBUG: Log errors
      if (process.env['POLLY_DEBUG']) {
        console.log(`[DEBUG] Error in extractTypeGuardHandlers: ${error}`)
      }
    }

    return handlers
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
      const ifStmt = ifNode as IfStatement
      // Get condition expression
      const condition = ifStmt.getExpression()

      // Check if condition is a call expression (function call)
      if (!Node.isCallExpression(condition)) {
        return null
      }

      // Get the function being called
      const funcExpr = condition.getExpression()
      let funcName: string | undefined

      if (Node.isIdentifier(funcExpr)) {
        funcName = funcExpr.getText()
      }

      if (process.env['POLLY_DEBUG'] && funcName) {
        console.log(`[DEBUG] Processing if condition with function: ${funcName}`)
      }

      // Try to find message type from local type guards first
      let messageType: string | undefined = undefined

      if (funcName && typeGuards.has(funcName)) {
        // Found in local file
        messageType = typeGuards.get(funcName)!

        if (process.env['POLLY_DEBUG']) {
          console.log(`[DEBUG] Found in local type guards: ${funcName} → ${messageType}`)
        }
      } else if (Node.isIdentifier(funcExpr)) {
        // Not found locally - try to resolve from imports
        if (process.env['POLLY_DEBUG']) {
          console.log(`[DEBUG] Not found locally, trying import resolution for: ${funcName}`)
        }

        messageType = this.resolveImportedTypeGuard(funcExpr) ?? undefined
      }

      if (!messageType) {
        if (process.env['POLLY_DEBUG'] && funcName) {
          console.log(`[DEBUG] Could not resolve message type for: ${funcName}`)
        }
        return null
      }

      // Found a type guard call! Use the message type
      const line = ifStmt.getStartLineNumber()

      // Extract relationships from the if block
      const sourceFile = ifStmt.getSourceFile()
      const handlerName = `${messageType}_handler`
      let relationships = undefined

      const thenStatement = ifStmt.getThenStatement()
      if (thenStatement) {
        const detectedRelationships = this.relationshipExtractor.extractFromHandler(
          thenStatement,
          sourceFile,
          handlerName
        )
        if (detectedRelationships.length > 0) {
          relationships = detectedRelationships
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
      }
    } catch (error) {
      return null
    }
  }

  /**
   * Find all type predicate functions in a source file
   * Returns a map of function name → message type
   * Uses AST-based detection for consistency with imported type guard resolution
   */
  private findTypePredicateFunctions(sourceFile: SourceFile): Map<string, string> {
    const typeGuards = new Map<string, string>()

    sourceFile.forEachDescendant((node) => {
      if (Node.isFunctionDeclaration(node) || Node.isFunctionExpression(node) || Node.isArrowFunction(node)) {
        // Check the return type NODE (AST structure) for type predicate
        const returnTypeNode = node.getReturnTypeNode()

        if (returnTypeNode && Node.isTypePredicate(returnTypeNode)) {
          // Extract function name
          let functionName: string | undefined
          if (Node.isFunctionDeclaration(node)) {
            functionName = node.getName()
          } else if (Node.isFunctionExpression(node)) {
            const parent = node.getParent()
            if (Node.isVariableDeclaration(parent)) {
              functionName = parent.getName()
            }
          } else if (Node.isArrowFunction(node)) {
            const parent = node.getParent()
            if (Node.isVariableDeclaration(parent)) {
              functionName = parent.getName()
            }
          }

          if (functionName) {
            // Extract the type from the type predicate node
            const typeNode = returnTypeNode.getTypeNode()
            let messageType: string | null = null

            if (typeNode) {
              const typeName = typeNode.getText()  // e.g., "QueryMessage"
              messageType = this.extractMessageTypeFromTypeName(typeName)
            }

            // Fallback: Analyze function body for msg.type === 'value'
            if (!messageType) {
              const body = node.getBody()
              if (body) {
                const bodyText = body.getText()
                const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/)
                if (typeValueMatch) {
                  messageType = typeValueMatch[1] ?? null
                }
              }
            }

            if (messageType) {
              typeGuards.set(functionName, messageType)
            }
          }
        }
      }
    })

    return typeGuards
  }

  /**
   * Resolve type guard from imported function
   * Uses ts-morph symbol resolution to find definition across files
   * Checks AST structure, not resolved types (which can lose type predicate info)
   */
  private resolveImportedTypeGuard(identifier: any): string | null {
    try {
      const funcName = identifier.getText()

      // Get the definition nodes (where the function is defined)
      const definitions = identifier.getDefinitionNodes()

      if (definitions.length === 0) {
        if (process.env['POLLY_DEBUG']) {
          console.log(`[DEBUG] No definitions found for imported function: ${funcName}`)
        }
        return null
      }

      for (const def of definitions) {
        // Check if it's a function with type predicate return type
        if (Node.isFunctionDeclaration(def) ||
            Node.isFunctionExpression(def) ||
            Node.isArrowFunction(def)) {

          // Check the return type NODE (AST structure), not the resolved TYPE
          // This is critical: ts-morph returns "boolean" for type predicates when checking .getReturnType()
          // but the AST node structure preserves the actual type predicate
          const returnTypeNode = def.getReturnTypeNode()

          if (process.env['POLLY_DEBUG']) {
            const returnType = def.getReturnType().getText()
            console.log(`[DEBUG] Function ${funcName} return type (resolved): ${returnType}`)
            console.log(`[DEBUG] Has return type node: ${!!returnTypeNode}`)
            console.log(`[DEBUG] Is type predicate node: ${returnTypeNode && Node.isTypePredicate(returnTypeNode)}`)
          }

          // Check if the return type node is a type predicate
          if (returnTypeNode && Node.isTypePredicate(returnTypeNode)) {
            // Extract the type from the type predicate node
            const typeNode = returnTypeNode.getTypeNode()

            if (typeNode) {
              const typeName = typeNode.getText()  // e.g., "QueryMessage"
              const messageType = this.extractMessageTypeFromTypeName(typeName)

              if (messageType) {
                if (process.env['POLLY_DEBUG']) {
                  console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from AST type predicate)`)
                }
                return messageType
              }
            }
          }

          // Fallback: Analyze function body for msg.type === 'value'
          const body = def.getBody()
          if (body) {
            const bodyText = body.getText()
            const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/)
            if (typeValueMatch) {
              const messageType = typeValueMatch[1] ?? null

              if (process.env['POLLY_DEBUG']) {
                console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from body)`)
              }

              return messageType
            }
          }
        }
      }
    } catch (error) {
      // DEBUG: Log errors
      if (process.env['POLLY_DEBUG']) {
        console.log(`[DEBUG] Error resolving imported type guard: ${error}`)
      }
    }

    return null
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
      .replace(/Message$/, '')
      .replace(/Event$/, '')
      .replace(/Request$/, '')
      .replace(/Command$/, '')
      .replace(/Query$/, '')
      .toLowerCase()

    return messageType
  }

  /**
   * Infer the context (background, content, popup, etc.) from file path
   */
  private inferContext(filePath: string): string {
    const path = filePath.toLowerCase()

    // Chrome extension contexts
    if (path.includes("/background/") || path.includes("\\background\\")) {
      return "background"
    }
    if (path.includes("/content/") || path.includes("\\content\\")) {
      return "content"
    }
    if (path.includes("/popup/") || path.includes("\\popup\\")) {
      return "popup"
    }
    if (path.includes("/devtools/") || path.includes("\\devtools\\")) {
      return "devtools"
    }
    if (path.includes("/options/") || path.includes("\\options\\")) {
      return "options"
    }
    if (path.includes("/offscreen/") || path.includes("\\offscreen\\")) {
      return "offscreen"
    }

    // WebSocket/server app contexts
    if (path.includes("/server/") || path.includes("\\server\\") || path.includes("/server.")) {
      return "server"
    }
    if (path.includes("/client/") || path.includes("\\client\\") || path.includes("/client.")) {
      return "client"
    }

    // PWA/Worker contexts
    if (path.includes("/worker/") || path.includes("\\worker\\") || path.includes("service-worker")) {
      return "worker"
    }

    return "unknown"
  }
}

export function extractHandlers(tsConfigPath: string): HandlerAnalysis {
  const extractor = new HandlerExtractor(tsConfigPath)
  return extractor.extractHandlers()
}
