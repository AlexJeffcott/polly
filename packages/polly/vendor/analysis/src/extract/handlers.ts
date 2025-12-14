// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations

import { Project, type SourceFile, SyntaxKind, Node } from "ts-morph"
import type { MessageHandler, StateAssignment, VerificationCondition } from "../types"

export interface HandlerAnalysis {
  handlers: MessageHandler[]
  messageTypes: Set<string>
}

export class HandlerExtractor {
  private project: Project
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
      compilerOptions: {
        // Allow .ts/.tsx extensions in imports (Bun/Deno style)
        allowImportingTsExtensions: true,
        // Use bundler module resolution (supports .ts extensions)
        moduleResolution: 99, // ModuleResolutionKind.Bundler
      },
    })
    this.typeGuardCache = new WeakMap()
  }

  /**
   * Extract all message handlers from the codebase
   */
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = []
    const messageTypes = new Set<string>()

    // Find all source files
    const sourceFiles = this.project.getSourceFiles()

    if (process.env.POLLY_DEBUG) {
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
        messageTypes.add(handler.messageType)
      }
    }

    if (process.env.POLLY_DEBUG) {
      console.log(`[DEBUG] Total handlers extracted: ${handlers.length}`)
    }

    return {
      handlers,
      messageTypes,
    }
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
      if (Node.isIfStatement(node)) {
        const typeGuardHandlers = this.extractTypeGuardHandlers(node, context, filePath)
        handlers.push(...typeGuardHandlers)
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

    statements.forEach((statement: any, index: number) => {
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
      if (process.env.POLLY_DEBUG) {
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
      let currentIf: Node = ifNode

      while (currentIf) {
        const handler = this.extractHandlerFromIfClause(currentIf, typeGuards, context, filePath)
        if (handler) {
          handlers.push(handler)

          if (process.env.POLLY_DEBUG) {
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
      if (process.env.POLLY_DEBUG) {
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
      // Get condition expression
      const condition = ifNode.getExpression()

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

      if (process.env.POLLY_DEBUG && funcName) {
        console.log(`[DEBUG] Processing if condition with function: ${funcName}`)
      }

      // Try to find message type from local type guards first
      let messageType: string | undefined = undefined

      if (funcName && typeGuards.has(funcName)) {
        // Found in local file
        messageType = typeGuards.get(funcName)!

        if (process.env.POLLY_DEBUG) {
          console.log(`[DEBUG] Found in local type guards: ${funcName} → ${messageType}`)
        }
      } else if (Node.isIdentifier(funcExpr)) {
        // Not found locally - try to resolve from imports
        if (process.env.POLLY_DEBUG) {
          console.log(`[DEBUG] Not found locally, trying import resolution for: ${funcName}`)
        }

        messageType = this.resolveImportedTypeGuard(funcExpr)
      }

      if (!messageType) {
        if (process.env.POLLY_DEBUG && funcName) {
          console.log(`[DEBUG] Could not resolve message type for: ${funcName}`)
        }
        return null
      }

      // Found a type guard call! Use the message type
      const line = ifNode.getStartLineNumber()

      return {
        messageType,
        node: context,
        assignments: [],
        preconditions: [],
        postconditions: [],
        location: { file: filePath, line },
      }
    } catch (error) {
      return null
    }
  }

  /**
   * Find all type predicate functions in a source file
   * Returns a map of function name → message type
   */
  private findTypePredicateFunctions(sourceFile: SourceFile): Map<string, string> {
    const typeGuards = new Map<string, string>()

    sourceFile.forEachDescendant((node) => {
      if (Node.isFunctionDeclaration(node) || Node.isFunctionExpression(node) || Node.isArrowFunction(node)) {
        const returnType = node.getReturnType()
        const returnTypeText = returnType.getText()

        // Check if return type is a type predicate: "arg is Type"
        if (/is\s+\w+/.test(returnTypeText)) {
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
            // Extract message type from:
            // 1. Type predicate: "msg is QueryMessage" → "query" or "QueryMessage"
            // 2. Function body: return msg.type === 'query'

            let messageType: string | null = null

            // Strategy 1: Parse from type predicate name
            // "msg is QueryMessage" → extract "QueryMessage"
            const typeMatch = returnTypeText.match(/is\s+(\w+)/)
            if (typeMatch) {
              const typeName = typeMatch[1]
              // Convert "QueryMessage" → "query"
              messageType = this.extractMessageTypeFromTypeName(typeName)
            }

            // Strategy 2: Analyze function body for msg.type === 'value'
            if (!messageType) {
              const body = node.getBody()
              if (body) {
                const bodyText = body.getText()
                const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/)
                if (typeValueMatch) {
                  messageType = typeValueMatch[1]
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
   */
  private resolveImportedTypeGuard(identifier: any): string | null {
    try {
      const funcName = identifier.getText()

      // Get the definition nodes (where the function is defined)
      const definitions = identifier.getDefinitionNodes()

      if (definitions.length === 0) {
        if (process.env.POLLY_DEBUG) {
          console.log(`[DEBUG] No definitions found for imported function: ${funcName}`)
        }
        return null
      }

      for (const def of definitions) {
        // Check if it's a function with type predicate return type
        if (Node.isFunctionDeclaration(def) ||
            Node.isFunctionExpression(def) ||
            Node.isArrowFunction(def)) {

          const returnType = def.getReturnType()
          const returnTypeText = returnType.getText()

          // DEBUG: Log return type
          if (process.env.POLLY_DEBUG) {
            console.log(`[DEBUG] Function ${funcName} return type: ${returnTypeText}`)
          }

          // Check for type predicate: "arg is Type"
          if (/is\s+\w+/.test(returnTypeText)) {
            // Strategy 1: Parse from type predicate name
            // "msg is QueryMessage" → extract "QueryMessage"
            const typeMatch = returnTypeText.match(/is\s+(\w+)/)
            if (typeMatch) {
              const typeName = typeMatch[1]
              // Convert "QueryMessage" → "query"
              const messageType = this.extractMessageTypeFromTypeName(typeName)

              if (process.env.POLLY_DEBUG) {
                console.log(`[DEBUG] Resolved ${funcName} → ${messageType}`)
              }

              return messageType
            }

            // Strategy 2: Analyze function body for msg.type === 'value'
            const body = def.getBody()
            if (body) {
              const bodyText = body.getText()
              const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/)
              if (typeValueMatch) {
                const messageType = typeValueMatch[1]

                if (process.env.POLLY_DEBUG) {
                  console.log(`[DEBUG] Resolved ${funcName} → ${messageType} (from body)`)
                }

                return messageType
              }
            }
          }
        }
      }
    } catch (error) {
      // DEBUG: Log errors
      if (process.env.POLLY_DEBUG) {
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
