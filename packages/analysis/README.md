# @fairfox/polly-analysis

Shared TypeScript analysis tools for static code analysis of message-passing systems.

## Overview

This package provides low-level utilities for analyzing TypeScript codebases, extracting types, message handlers, and other structural information. It's used as a foundation for both `@fairfox/polly-verify` and `@fairfox/polly-visualize`.

## Features

- **Type Extraction:** Extract TypeScript type information using ts-morph
- **Handler Analysis:** Find and analyze message handlers (`.on()` patterns)
- **State Analysis:** Analyze state types and mutations
- **Verification Conditions:** Extract `requires()` and `ensures()` conditions
- **Context Inference:** Infer execution context from file paths

## Usage

```typescript
import { TypeExtractor, HandlerExtractor, analyzeCodebase } from '@fairfox/polly-analysis'

// Analyze entire codebase
const analysis = await analyzeCodebase({
  tsConfigPath: "./tsconfig.json",
  stateFilePath: "./src/state.ts"
})

console.log(analysis.stateType)      // Extracted state type
console.log(analysis.messageTypes)   // Found message types
console.log(analysis.handlers)       // Message handlers
console.log(analysis.fields)         // State field analysis

// Or use extractors directly
const typeExtractor = new TypeExtractor("./tsconfig.json")
const handlerExtractor = new HandlerExtractor("./tsconfig.json")
```

## Types

### CodebaseAnalysis

Complete analysis result:

```typescript
type CodebaseAnalysis = {
  stateType: TypeInfo | null
  messageTypes: string[]
  fields: FieldAnalysis[]
  handlers: MessageHandler[]
}
```

### TypeInfo

Represents a TypeScript type:

```typescript
type TypeInfo = {
  name: string
  kind: TypeKind
  nullable: boolean
  elementType?: TypeInfo  // For arrays, sets
  valueType?: TypeInfo    // For maps
  properties?: Record<string, TypeInfo>  // For objects
  enumValues?: string[]   // For enums
  unionTypes?: TypeInfo[] // For unions
}
```

### MessageHandler

Represents an extracted message handler:

```typescript
type MessageHandler = {
  messageType: string
  node: string
  assignments: StateAssignment[]
  preconditions: VerificationCondition[]
  postconditions: VerificationCondition[]
  location: { file: string; line: number }
}
```

## License

MIT
