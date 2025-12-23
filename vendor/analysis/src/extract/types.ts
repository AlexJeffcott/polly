// Type extraction from TypeScript using ts-morph

import { Project, Type } from "ts-morph"
import type { TypeInfo, FieldAnalysis, CodebaseAnalysis } from "../types"
import { HandlerExtractor } from "./handlers"

export class TypeExtractor {
  private project: Project

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    })
  }

  /**
   * Analyze the codebase and extract state types and message types
   */
  async analyzeCodebase(stateFilePath?: string): Promise<CodebaseAnalysis> {
    // Find state type
    const stateType = stateFilePath
      ? this.extractStateType(stateFilePath)
      : this.findStateType()

    // Find message types
    const messageTypes = this.findMessageTypes()

    // Analyze fields
    const fields = stateType ? this.analyzeFields(stateType) : []

    // Extract message handlers
    const configFilePath = this.project.getCompilerOptions()['configFilePath']
    const tsConfigPath = typeof configFilePath === "string" ? configFilePath : "tsconfig.json"
    const handlerExtractor = new HandlerExtractor(tsConfigPath)
    const handlerAnalysis = handlerExtractor.extractHandlers()

    // Combine and filter message types to only include valid TLA+ identifiers
    const allMessageTypes = Array.from(new Set([...messageTypes, ...handlerAnalysis.messageTypes]))
    const validMessageTypes: string[] = []
    const invalidMessageTypes: string[] = []

    for (const msgType of allMessageTypes) {
      if (this.isValidTLAIdentifier(msgType)) {
        validMessageTypes.push(msgType)
      } else {
        invalidMessageTypes.push(msgType)
      }
    }

    // Log warnings about invalid message types
    if (invalidMessageTypes.length > 0 && process.env['POLLY_DEBUG']) {
      console.log(`[WARN] Filtered out ${invalidMessageTypes.length} invalid message type(s):`)
      for (const invalid of invalidMessageTypes) {
        console.log(`[WARN]   - "${invalid}" (not a valid TLA+ identifier)`)
      }
    }

    return {
      stateType,
      messageTypes: validMessageTypes,
      fields,
      handlers: handlerAnalysis.handlers,
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
   * Extract state type from a specific file
   */
  private extractStateType(filePath: string): TypeInfo | null {
    const sourceFile = this.project.getSourceFile(filePath)
    if (!sourceFile) {
      return null
    }

    // Look for type alias named "AppState" or similar
    const typeAlias = sourceFile.getTypeAlias("AppState")
      || sourceFile.getTypeAlias("State")
      || sourceFile.getTypeAliases()[0]

    if (!typeAlias) {
      return null
    }

    const type = typeAlias.getType()
    return this.convertType(type, typeAlias.getName())
  }

  /**
   * Find state type by searching common patterns
   */
  private findStateType(): TypeInfo | null {
    // Search for files with "state" in the name
    const stateFiles = this.project.getSourceFiles("**/state*.ts")

    for (const file of stateFiles) {
      const typeAlias = file.getTypeAlias("AppState")
        || file.getTypeAlias("State")

      if (typeAlias) {
        const type = typeAlias.getType()
        return this.convertType(type, typeAlias.getName())
      }
    }

    return null
  }

  /**
   * Find message types by searching for type unions
   */
  private findMessageTypes(): string[] {
    const messageTypes: string[] = []

    // Search for files with "message" in the name
    const messageFiles = this.project.getSourceFiles("**/message*.ts")

    for (const file of messageFiles) {
      // Look for type aliases that are unions
      for (const typeAlias of file.getTypeAliases()) {
        const type = typeAlias.getType()
        if (type.isUnion()) {
          // Extract message type literals
          for (const unionType of type.getUnionTypes()) {
            if (unionType.isObject()) {
              const typeProperty = unionType.getProperty("type")
              if (typeProperty) {
                const typeType = typeProperty.getTypeAtLocation(file)
                if (typeType.isStringLiteral()) {
                  messageTypes.push(typeType.getLiteralValue() as string)
                }
              }
            }
          }
        }
      }
    }

    return [...new Set(messageTypes)] // Dedupe
  }

  /**
   * Convert ts-morph Type to our TypeInfo
   */
  private convertType(type: Type, name: string): TypeInfo {
    // Check for null/undefined
    const nullable = type.isNullable()

    // Boolean
    if (type.isBoolean() || type.isBooleanLiteral()) {
      return { name, kind: "boolean", nullable }
    }

    // Union types
    if (type.isUnion()) {
      const unionTypes = type.getUnionTypes()

      // Check for string literal union (enum)
      const allStringLiterals = unionTypes.every(t => t.isStringLiteral())
      if (allStringLiterals) {
        const enumValues = unionTypes.map(t => t.getLiteralValue() as string)
        return {
          name,
          kind: "enum",
          nullable,
          enumValues
        }
      }

      // Check for nullable type (T | null | undefined)
      const nonNullTypes = unionTypes.filter(t => !t.isNull() && !t.isUndefined())

      if (nonNullTypes.length === 1) {
        // This is a nullable type: T | null or T | undefined
        const baseType = this.convertType(nonNullTypes[0]!, name)
        return {
          ...baseType,
          nullable: true
        }
      }

      // Generic union - keep as-is
      return {
        name,
        kind: "union",
        nullable,
        unionTypes: unionTypes.map((t, i) => this.convertType(t, `${name}_${i}`))
      }
    }

    // String
    if (type.isString() || type.isStringLiteral()) {
      return { name, kind: "string", nullable }
    }

    // Number
    if (type.isNumber() || type.isNumberLiteral()) {
      return { name, kind: "number", nullable }
    }

    // Array
    if (type.isArray()) {
      const elementType = type.getArrayElementType()
      return {
        name,
        kind: "array",
        nullable,
        elementType: elementType
          ? this.convertType(elementType, `${name}_element`)
          : { name: "unknown", kind: "unknown", nullable: false }
      }
    }

    // Map/Set detection - must come before generic object handling
    const symbol = type.getSymbol()
    if (symbol) {
      const symbolName = symbol.getName()

      // Map<K, V>
      if (symbolName === "Map") {
        const typeArgs = type.getTypeArguments()
        return {
          name,
          kind: "map",
          nullable,
          // Extract value type from Map<K, V>
          valueType: typeArgs && typeArgs[1]
            ? this.convertType(typeArgs[1], `${name}_value`)
            : undefined
        }
      }

      // Set<T>
      if (symbolName === "Set") {
        const typeArgs = type.getTypeArguments()
        return {
          name,
          kind: "set",
          nullable,
          elementType: typeArgs && typeArgs[0]
            ? this.convertType(typeArgs[0], `${name}_element`)
            : undefined
        }
      }
    }

    // Object
    if (type.isObject()) {
      const properties: Record<string, TypeInfo> = {}
      const sourceFile = this.project.getSourceFiles()[0]

      if (sourceFile) {
        for (const prop of type.getProperties()) {
          const propName = prop.getName()
          const propType = prop.getTypeAtLocation(sourceFile)
          properties[propName] = this.convertType(propType, propName)
        }
      }

      return {
        name,
        kind: "object",
        nullable,
        properties
      }
    }

    // Null
    if (type.isNull()) {
      return { name, kind: "null", nullable: true }
    }

    // Unknown/Any
    return { name, kind: "unknown", nullable }
  }

  /**
   * Analyze fields and determine confidence/bounds
   */
  private analyzeFields(stateType: TypeInfo, prefix = ""): FieldAnalysis[] {
    const fields: FieldAnalysis[] = []

    if (stateType.kind === "object" && stateType.properties) {
      for (const [key, propType] of Object.entries(stateType.properties)) {
        const path = prefix ? `${prefix}.${key}` : key

        // Recursively analyze nested objects (but not Map/Set - they're leaf nodes)
        if (propType.kind === "object") {
          // Don't add intermediate objects as fields, just recurse into them
          fields.push(...this.analyzeFields(propType, path))
        } else {
          // This is a leaf field (or Map/Set), add it for configuration
          const analysis = this.analyzeField(path, propType)
          fields.push(analysis)
        }
      }
    }

    return fields
  }

  /**
   * Analyze a single field and determine configuration needs
   */
  private analyzeField(path: string, type: TypeInfo): FieldAnalysis {
    const analysis: FieldAnalysis = {
      path,
      type,
      confidence: "low",
      evidence: [],
      suggestions: [],
      bounds: {}
    }

    // Boolean - high confidence, no config needed
    if (type.kind === "boolean") {
      analysis.confidence = "high"
      analysis.evidence.push("Boolean type - auto-configured")
      return analysis
    }

    // Enum - high confidence
    if (type.kind === "enum" && type.enumValues) {
      analysis.confidence = "high"
      analysis.evidence.push(`Enum with ${type.enumValues.length} values`)
      analysis.bounds!.values = type.enumValues
      return analysis
    }

    // Array - needs manual configuration
    if (type.kind === "array") {
      analysis.confidence = "low"
      analysis.suggestions.push(
        "Choose maxLength: 5 (fast), 10 (balanced), or 20 (thorough)"
      )
      analysis.bounds!.maxLength = undefined

      // Try to find bounds in code
      const foundBound = this.findArrayBound()
      if (foundBound) {
        analysis.confidence = "medium"
        analysis.evidence.push(`Found array check: ${foundBound.evidence}`)
        analysis.bounds!.maxLength = foundBound.value
      }

      return analysis
    }

    // Number - needs manual configuration
    if (type.kind === "number") {
      analysis.confidence = "low"
      analysis.suggestions.push("Provide min and max values based on your application logic")
      analysis.bounds!.min = undefined
      analysis.bounds!.max = undefined

      // Try to find bounds in code
      const foundBound = this.findNumberBound()
      if (foundBound) {
        analysis.confidence = "high"
        analysis.evidence.push(`Found comparison: ${foundBound.evidence}`)
        analysis.bounds = { ...analysis.bounds!, ...foundBound.bounds }
      }

      return analysis
    }

    // String - needs manual configuration
    if (type.kind === "string") {
      analysis.confidence = "low"
      analysis.suggestions.push(
        'Provide 2-3 example values: ["value1", "value2", "value3"]',
        "Or use { abstract: true } for symbolic verification"
      )
      analysis.bounds!.values = undefined
      return analysis
    }

    // Map/Set - needs manual configuration
    if (type.kind === "map" || type.kind === "set") {
      analysis.confidence = "low"
      analysis.suggestions.push("Provide maxSize (recommended: 3-5)")
      analysis.bounds!.maxSize = undefined
      return analysis
    }

    return analysis
  }

  /**
   * Try to find array bounds by searching for length checks
   */
  private findArrayBound(): { value: number; evidence: string } | null {
    // TODO: Search source code for patterns like:
    // - if (array.length < N)
    // - array.slice(0, N)
    // This would require analyzing the actual usage in code
    return null
  }

  /**
   * Try to find number bounds by searching for comparisons
   */
  private findNumberBound(): { bounds: { min?: number; max?: number }; evidence: string } | null {
    // TODO: Search source code for patterns like:
    // - if (counter < 100)
    // - if (value >= 0 && value <= 100)
    // This would require analyzing the actual usage in code
    return null
  }
}

export async function analyzeCodebase(options: {
  tsConfigPath: string
  stateFilePath?: string
}): Promise<CodebaseAnalysis> {
  const extractor = new TypeExtractor(options.tsConfigPath)
  return extractor.analyzeCodebase(options.stateFilePath)
}
