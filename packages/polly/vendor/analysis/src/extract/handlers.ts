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

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    })
  }

  /**
   * Extract all message handlers from the codebase
   */
  extractHandlers(): HandlerAnalysis {
    const handlers: MessageHandler[] = []
    const messageTypes = new Set<string>()

    // Find all source files
    const sourceFiles = this.project.getSourceFiles()

    for (const sourceFile of sourceFiles) {
      const fileHandlers = this.extractFromFile(sourceFile)
      handlers.push(...fileHandlers)

      for (const handler of fileHandlers) {
        messageTypes.add(handler.messageType)
      }
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

    // Find all .on() call expressions
    sourceFile.forEachDescendant((node) => {
      if (Node.isCallExpression(node)) {
        const expression = node.getExpression()

        // Check if this is a .on() call
        if (Node.isPropertyAccessExpression(expression)) {
          const methodName = expression.getName()

          if (methodName === "on") {
            const handler = this.extractHandler(node, context, filePath)
            if (handler) {
              handlers.push(handler)
            }
          }
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
