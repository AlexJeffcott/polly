# Type Guard Handler Detection - Implementation Draft

## Overview

This document outlines the implementation for detecting TypeScript type guard patterns in message handlers.

## Code Location

File: `packages/polly/vendor/analysis/src/extract/handlers.ts`

## Changes Required

### 1. Add Type Guard Detection to `extractFromFile()`

Insert after line 84 (after Pattern 3 handler map detection):

```typescript
// Pattern 4: Type guard if/else-if chains
if (Node.isIfStatement(node)) {
  const typeGuardHandlers = this.extractTypeGuardHandlers(node, context, filePath)
  handlers.push(...typeGuardHandlers)
}
```

### 2. Add Helper Method: `findTypePredicateFunctions()`

Add after `extractHandlerMapPattern()` method:

```typescript
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
```

### 3. Add Helper Method: `extractMessageTypeFromTypeName()`

```typescript
/**
 * Extract message type from TypeScript type name
 * Examples:
 *   QueryMessage → query
 *   CommandMessage → command
 *   SubscribeMessage → subscribe
 */
private extractMessageTypeFromTypeName(typeName: string): string {
  // Remove common suffixes
  let messageType = typeName
    .replace(/Message$/, '')
    .replace(/Event$/, '')
    .replace(/Request$/, '')
    .replace(/Command$/, '')
    .replace(/Query$/, '')

  // Convert PascalCase to lowercase
  messageType = messageType
    .replace(/([A-Z])/g, (match, char) => char.toLowerCase())

  return messageType
}
```

### 4. Add Main Method: `extractTypeGuardHandlers()`

```typescript
/**
 * Extract handlers from type guard if/else-if patterns
 * Detects: if (isQueryMessage(msg)) { handleQuery(msg); }
 */
private extractTypeGuardHandlers(
  ifNode: any,
  context: string,
  filePath: string
): MessageHandler[] {
  const handlers: MessageHandler[] = []

  try {
    // Get the source file to find type predicates
    const sourceFile = ifNode.getSourceFile()
    const typeGuards = this.findTypePredicateFunctions(sourceFile)

    if (typeGuards.size === 0) {
      return handlers
    }

    // Process the if statement and all else-if chains
    let currentIf: any = ifNode

    while (currentIf) {
      const handler = this.extractHandlerFromIfClause(currentIf, typeGuards, context, filePath)
      if (handler) {
        handlers.push(handler)
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
    // Skip malformed if statements
  }

  return handlers
}

/**
 * Extract handler from a single if clause
 */
private extractHandlerFromIfClause(
  ifNode: any,
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

    if (!funcName || !typeGuards.has(funcName)) {
      return null
    }

    // Found a type guard call! Extract message type
    const messageType = typeGuards.get(funcName)!
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
```

## Testing Strategy

### Test File Location
`packages/polly/vendor/analysis/__tests__/handlers.test.ts`

### Test Cases to Add

```typescript
describe('Type Guard Handler Detection', () => {
  test('detects simple type guard pattern', () => {
    const code = `
      function isQuery(msg: Message): msg is QueryMessage {
        return msg.type === 'query'
      }

      if (isQuery(message)) {
        handleQuery(message)
      }
    `
    // Assert: 1 handler detected with type "query"
  })

  test('detects chained type guards', () => {
    const code = `
      function isQuery(msg: Message): msg is QueryMessage {
        return msg.type === 'query'
      }

      function isCommand(msg: Message): msg is CommandMessage {
        return msg.type === 'command'
      }

      if (isQuery(message)) {
        handleQuery(message)
      } else if (isCommand(message)) {
        handleCommand(message)
      }
    `
    // Assert: 2 handlers detected ("query", "command")
  })

  test('extracts message type from type name', () => {
    const code = `
      function isQueryMessage(msg: Message): msg is QueryMessage {
        return msg.type === 'query'
      }

      if (isQueryMessage(message)) {
        handleQuery(message)
      }
    `
    // Assert: message type is "query" (extracted from "QueryMessage")
  })

  test('handles nested type guards', () => {
    const code = `
      if (isAuthenticated(ws)) {
        if (isQuery(message)) {
          handleQuery(message)
        }
      }
    `
    // Assert: 1 handler detected even when nested
  })
})
```

## Integration with Lingua

The implementation should detect these patterns from Lingua's codebase:

**Location**: `packages/api/src/server.ts:168-192`

**Expected Results**:
```
✓ Found 1 context(s)
✓ Found 4 message flow(s)  ← NEW!
✓ Found 38 integration(s)

Contexts:
  • server
    - 4 handler(s)  ← NEW!
      * query
      * command
      * subscribe
      * unsubscribe
```

## Implementation Steps

1. ✅ Study existing handler detection patterns
2. ⏭️ Add type guard detection methods to handlers.ts
3. ⏭️ Add test cases for type guard patterns
4. ⏭️ Test with Lingua codebase
5. ⏭️ Create PR with changes

## Notes

- The implementation follows the same error-handling pattern as existing methods (try/catch)
- Returns empty array on malformed code to avoid breaking existing functionality
- Compatible with existing switch/case and handler map detection
- Should work alongside other pattern detection methods
