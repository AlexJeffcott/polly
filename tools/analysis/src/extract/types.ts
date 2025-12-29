// Type extraction from TypeScript using ts-morph

import { Project, type SourceFile, type Type } from "ts-morph";
import type { CodebaseAnalysis, FieldAnalysis, TypeInfo } from "../types";
import { HandlerExtractor } from "./handlers";

export class TypeExtractor {
  private project: Project;

  constructor(tsConfigPath: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
    });
  }

  /**
   * Analyze the codebase and extract state types and message types
   */
  async analyzeCodebase(stateFilePath?: string): Promise<CodebaseAnalysis> {
    // Find state type
    const stateType = stateFilePath ? this.extractStateType(stateFilePath) : this.findStateType();

    // Find message types
    const messageTypes = this.findMessageTypes();

    // Analyze fields
    const fields = stateType ? this.analyzeFields(stateType) : [];

    // Extract message handlers
    const configFilePath = this.project.getCompilerOptions()["configFilePath"];
    const tsConfigPath = typeof configFilePath === "string" ? configFilePath : "tsconfig.json";
    const handlerExtractor = new HandlerExtractor(tsConfigPath);
    const handlerAnalysis = handlerExtractor.extractHandlers();

    // Combine and filter message types to only include valid TLA+ identifiers
    const allMessageTypes = Array.from(new Set([...messageTypes, ...handlerAnalysis.messageTypes]));
    const validMessageTypes: string[] = [];
    const invalidMessageTypes: string[] = [];

    for (const msgType of allMessageTypes) {
      if (this.isValidTLAIdentifier(msgType)) {
        validMessageTypes.push(msgType);
      } else {
        invalidMessageTypes.push(msgType);
      }
    }

    // Log warnings about invalid message types
    if (invalidMessageTypes.length > 0 && process.env["POLLY_DEBUG"]) {
      console.log(`[WARN] Filtered out ${invalidMessageTypes.length} invalid message type(s):`);
      for (const invalid of invalidMessageTypes) {
        console.log(`[WARN]   - "${invalid}" (not a valid TLA+ identifier)`);
      }
    }

    return {
      stateType,
      messageTypes: validMessageTypes,
      fields,
      handlers: handlerAnalysis.handlers,
    };
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
   * Extract state type from a specific file
   */
  private extractStateType(filePath: string): TypeInfo | null {
    const sourceFile = this.project.getSourceFile(filePath);
    if (!sourceFile) {
      return null;
    }

    // Look for type alias named "AppState" or similar
    const typeAlias =
      sourceFile.getTypeAlias("AppState") ||
      sourceFile.getTypeAlias("State") ||
      sourceFile.getTypeAliases()[0];

    if (!typeAlias) {
      return null;
    }

    const type = typeAlias.getType();
    return this.convertType(type, typeAlias.getName());
  }

  /**
   * Find state type by searching common patterns
   */
  private findStateType(): TypeInfo | null {
    // Search for files with "state" in the name
    const stateFiles = this.project.getSourceFiles("**/state*.ts");

    for (const file of stateFiles) {
      const typeAlias = file.getTypeAlias("AppState") || file.getTypeAlias("State");

      if (typeAlias) {
        const type = typeAlias.getType();
        return this.convertType(type, typeAlias.getName());
      }
    }

    return null;
  }

  /**
   * Find message types by searching for type unions
   * Handles:
   * - Simple string literal unions
   * - Discriminated unions ({ type: 'foo' } | { type: 'bar' })
   * - Type aliases across files
   * - Template literal types (with warning)
   * - Conditional types (conservatively)
   * - Mapped types
   */
  private findMessageTypes(): string[] {
    const messageTypes: string[] = [];
    const warnings: string[] = [];

    // Search for files with "message" in the name
    const messageFiles = this.project.getSourceFiles("**/message*.ts");

    for (const file of messageFiles) {
      // Look for type aliases that might contain message types
      for (const typeAlias of file.getTypeAliases()) {
        const extractedTypes = this.extractMessageTypesFromType(
          typeAlias.getType(),
          typeAlias.getName(),
          file,
          warnings
        );
        messageTypes.push(...extractedTypes);
      }
    }

    // Log warnings about unbounded types
    if (warnings.length > 0 && process.env["POLLY_DEBUG"]) {
      console.log("[WARN] Message type extraction warnings:");
      for (const warning of warnings) {
        console.log(`[WARN]   ${warning}`);
      }
    }

    return [...new Set(messageTypes)]; // Dedupe
  }

  /**
   * Extract message types from a TypeScript type
   * Recursively handles unions, discriminated unions, aliases, etc.
   */
  private extractMessageTypesFromType(
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): string[] {
    if (type.isUnion()) {
      return this.extractFromUnionType(type, typeName, sourceFile, warnings);
    }

    if (type.getAliasSymbol()) {
      return this.extractFromTypeAlias(type, typeName, sourceFile, warnings);
    }

    if (type.isConditionalType?.()) {
      return this.extractFromConditionalType(type, warnings);
    }

    if (type.getText().includes("[K in ")) {
      return this.extractFromMappedType(type, sourceFile, warnings);
    }

    if (type.getText().includes("`")) {
      this.warnTemplateLiteral(type, warnings);
      return [];
    }

    return [];
  }

  /**
   * Extract message types from union type
   */
  private extractFromUnionType(
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): string[] {
    const messageTypes: string[] = [];
    const unionTypes = type.getUnionTypes();

    for (const unionType of unionTypes) {
      const extracted = this.extractFromUnionMember(unionType, typeName, sourceFile, warnings);
      messageTypes.push(...extracted);
    }

    return messageTypes;
  }

  /**
   * Extract message types from a single union member
   */
  private extractFromUnionMember(
    unionType: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): string[] {
    if (unionType.isObject()) {
      return this.extractFromDiscriminatedUnion(unionType, sourceFile, warnings);
    }

    if (unionType.isStringLiteral()) {
      return [unionType.getLiteralValue() as string];
    }

    if (unionType.getAliasSymbol()) {
      const aliasedType = unionType.getAliasSymbol()?.getDeclaredType();
      if (aliasedType) {
        return this.extractMessageTypesFromType(aliasedType, typeName, sourceFile, warnings);
      }
    }

    return [];
  }

  /**
   * Extract message types from discriminated union
   */
  private extractFromDiscriminatedUnion(
    unionType: Type,
    sourceFile: SourceFile,
    warnings: string[]
  ): string[] {
    const typeProperty = unionType.getProperty("type");
    if (!typeProperty) {
      return [];
    }

    const typeType = typeProperty.getTypeAtLocation(sourceFile);

    if (typeType.isStringLiteral()) {
      return [typeType.getLiteralValue() as string];
    }

    if (typeType.getText().includes("`")) {
      warnings.push(
        `Template literal type in discriminant: ${typeType.getText()} - may be unbounded`
      );
    }

    return [];
  }

  /**
   * Extract message types from type alias
   */
  private extractFromTypeAlias(
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): string[] {
    const aliasedType = type.getAliasSymbol()?.getDeclaredType();
    if (!aliasedType || aliasedType === type) {
      return [];
    }

    return this.extractMessageTypesFromType(aliasedType, typeName, sourceFile, warnings);
  }

  /**
   * Extract message types from conditional type
   */
  private extractFromConditionalType(type: Type, warnings: string[]): string[] {
    warnings.push(`Conditional type detected: ${type.getText()} - extracting conservatively`);

    const messageTypes: string[] = [];
    const typeText = type.getText();
    const parts = typeText.split("?");

    if (parts.length < 2) {
      return messageTypes;
    }

    const branches = parts[1].split(":");
    for (const branch of branches) {
      const extracted = this.extractStringLiteralFromBranch(branch);
      if (extracted) {
        messageTypes.push(extracted);
      }
    }

    return messageTypes;
  }

  /**
   * Extract string literal from conditional branch
   */
  private extractStringLiteralFromBranch(branch: string): string | null {
    const trimmed = branch.trim();
    const match = trimmed.match(/^["'](\w+)["']$/);
    return match?.[1] ?? null;
  }

  /**
   * Extract message types from mapped type
   */
  private extractFromMappedType(type: Type, sourceFile: SourceFile, warnings: string[]): string[] {
    warnings.push(`Mapped type detected: ${type.getText()} - attempting to extract keys`);

    const match = type.getText().match(/\[K in ([^\]]+)\]/);
    if (!match?.[1]) {
      return [];
    }

    const keyTypeName = match[1].trim();
    const keyTypeAlias = sourceFile.getTypeAlias?.(keyTypeName);

    if (!keyTypeAlias) {
      return [];
    }

    const keyType = keyTypeAlias.getType();
    return this.extractMessageTypesFromType(keyType, keyTypeName, sourceFile, warnings);
  }

  /**
   * Warn about template literal types
   */
  private warnTemplateLiteral(type: Type, warnings: string[]): void {
    warnings.push(
      `Template literal type: ${type.getText()} - this creates an unbounded set and cannot be fully extracted`
    );
  }

  /**
   * Convert ts-morph Type to our TypeInfo
   */
  private convertType(type: Type, name: string): TypeInfo {
    const nullable = type.isNullable();

    if (type.isBoolean() || type.isBooleanLiteral()) {
      return { name, kind: "boolean", nullable };
    }

    if (type.isUnion()) {
      return this.convertUnionType(type, name, nullable);
    }

    if (type.isString() || type.isStringLiteral()) {
      return { name, kind: "string", nullable };
    }

    if (type.isNumber() || type.isNumberLiteral()) {
      return { name, kind: "number", nullable };
    }

    if (type.isArray()) {
      return this.convertArrayType(type, name, nullable);
    }

    const collectionType = this.tryConvertCollectionType(type, name, nullable);
    if (collectionType) {
      return collectionType;
    }

    if (type.isObject()) {
      return this.convertObjectType(type, name, nullable);
    }

    if (type.isNull()) {
      return { name, kind: "null", nullable: true };
    }

    return { name, kind: "unknown", nullable };
  }

  /**
   * Convert union type to TypeInfo
   */
  private convertUnionType(type: Type, name: string, nullable: boolean): TypeInfo {
    const unionTypes = type.getUnionTypes();

    // Check for string literal union (enum)
    const allStringLiterals = unionTypes.every((t) => t.isStringLiteral());
    if (allStringLiterals) {
      const enumValues = unionTypes.map((t) => t.getLiteralValue() as string);
      return { name, kind: "enum", nullable, enumValues };
    }

    // Check for nullable type (T | null | undefined)
    const nonNullTypes = unionTypes.filter((t) => !t.isNull() && !t.isUndefined());

    if (nonNullTypes.length === 1) {
      const firstType = nonNullTypes[0];
      if (firstType) {
        const baseType = this.convertType(firstType, name);
        return { ...baseType, nullable: true };
      }
    }

    // Generic union
    return {
      name,
      kind: "union",
      nullable,
      unionTypes: unionTypes.map((t, i) => this.convertType(t, `${name}_${i}`)),
    };
  }

  /**
   * Convert array type to TypeInfo
   */
  private convertArrayType(type: Type, name: string, nullable: boolean): TypeInfo {
    const elementType = type.getArrayElementType();
    return {
      name,
      kind: "array",
      nullable,
      elementType: elementType
        ? this.convertType(elementType, `${name}_element`)
        : { name: "unknown", kind: "unknown", nullable: false },
    };
  }

  /**
   * Try to convert Map or Set type to TypeInfo
   */
  private tryConvertCollectionType(type: Type, name: string, nullable: boolean): TypeInfo | null {
    const symbol = type.getSymbol();
    if (!symbol) return null;

    const symbolName = symbol.getName();

    if (symbolName === "Map") {
      const typeArgs = type.getTypeArguments();
      return {
        name,
        kind: "map",
        nullable,
        valueType: typeArgs?.[1] ? this.convertType(typeArgs[1], `${name}_value`) : undefined,
      };
    }

    if (symbolName === "Set") {
      const typeArgs = type.getTypeArguments();
      return {
        name,
        kind: "set",
        nullable,
        elementType: typeArgs?.[0] ? this.convertType(typeArgs[0], `${name}_element`) : undefined,
      };
    }

    return null;
  }

  /**
   * Convert object type to TypeInfo
   */
  private convertObjectType(type: Type, name: string, nullable: boolean): TypeInfo {
    const properties: Record<string, TypeInfo> = {};
    const sourceFile = this.project.getSourceFiles()[0];

    if (sourceFile) {
      for (const prop of type.getProperties()) {
        const propName = prop.getName();
        const propType = prop.getTypeAtLocation(sourceFile);
        properties[propName] = this.convertType(propType, propName);
      }
    }

    return { name, kind: "object", nullable, properties };
  }

  /**
   * Analyze fields and determine confidence/bounds
   */
  private analyzeFields(stateType: TypeInfo, prefix = ""): FieldAnalysis[] {
    const fields: FieldAnalysis[] = [];

    if (stateType.kind === "object" && stateType.properties) {
      for (const [key, propType] of Object.entries(stateType.properties)) {
        const path = prefix ? `${prefix}.${key}` : key;

        // Recursively analyze nested objects (but not Map/Set - they're leaf nodes)
        if (propType.kind === "object") {
          // Don't add intermediate objects as fields, just recurse into them
          fields.push(...this.analyzeFields(propType, path));
        } else {
          // This is a leaf field (or Map/Set), add it for configuration
          const analysis = this.analyzeField(path, propType);
          fields.push(analysis);
        }
      }
    }

    return fields;
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
      bounds: {},
    };

    if (type.kind === "boolean") return this.analyzeBooleanField(analysis);
    if (type.kind === "enum") return this.analyzeEnumField(analysis, type);
    if (type.kind === "array") return this.analyzeArrayField(analysis);
    if (type.kind === "number") return this.analyzeNumberField(analysis);
    if (type.kind === "string") return this.analyzeStringField(analysis);
    if (type.kind === "map" || type.kind === "set") return this.analyzeMapSetField(analysis);

    return analysis;
  }

  private analyzeBooleanField(analysis: FieldAnalysis): FieldAnalysis {
    analysis.confidence = "high";
    analysis.evidence.push("Boolean type - auto-configured");
    return analysis;
  }

  private analyzeEnumField(analysis: FieldAnalysis, type: TypeInfo): FieldAnalysis {
    if (type.enumValues) {
      analysis.confidence = "high";
      analysis.evidence.push(`Enum with ${type.enumValues.length} values`);
      if (analysis.bounds) {
        analysis.bounds.values = type.enumValues;
      }
    }
    return analysis;
  }

  private analyzeArrayField(analysis: FieldAnalysis): FieldAnalysis {
    analysis.confidence = "low";
    analysis.suggestions.push("Choose maxLength: 5 (fast), 10 (balanced), or 20 (thorough)");
    if (analysis.bounds) {
      analysis.bounds.maxLength = undefined;
    }

    const foundBound = this.findArrayBound();
    if (foundBound && analysis.bounds) {
      analysis.confidence = "medium";
      analysis.evidence.push(`Found array check: ${foundBound.evidence}`);
      analysis.bounds.maxLength = foundBound.value;
    }

    return analysis;
  }

  private analyzeNumberField(analysis: FieldAnalysis): FieldAnalysis {
    analysis.confidence = "low";
    analysis.suggestions.push("Provide min and max values based on your application logic");
    if (analysis.bounds) {
      analysis.bounds.min = undefined;
      analysis.bounds.max = undefined;
    }

    const foundBound = this.findNumberBound();
    if (foundBound && analysis.bounds) {
      analysis.confidence = "high";
      analysis.evidence.push(`Found comparison: ${foundBound.evidence}`);
      analysis.bounds = { ...analysis.bounds, ...foundBound.bounds };
    }

    return analysis;
  }

  private analyzeStringField(analysis: FieldAnalysis): FieldAnalysis {
    analysis.confidence = "low";
    analysis.suggestions.push(
      'Provide 2-3 example values: ["value1", "value2", "value3"]',
      "Or use { abstract: true } for symbolic verification"
    );
    if (analysis.bounds) {
      analysis.bounds.values = undefined;
    }
    return analysis;
  }

  private analyzeMapSetField(analysis: FieldAnalysis): FieldAnalysis {
    analysis.confidence = "low";
    analysis.suggestions.push("Provide maxSize (recommended: 3-5)");
    if (analysis.bounds) {
      analysis.bounds.maxSize = undefined;
    }
    return analysis;
  }

  /**
   * Try to find array bounds by searching for length checks
   */
  private findArrayBound(): { value: number; evidence: string } | null {
    // TODO: Search source code for patterns like:
    // - if (array.length < N)
    // - array.slice(0, N)
    // This would require analyzing the actual usage in code
    return null;
  }

  /**
   * Try to find number bounds by searching for comparisons
   */
  private findNumberBound(): { bounds: { min?: number; max?: number }; evidence: string } | null {
    // TODO: Search source code for patterns like:
    // - if (counter < 100)
    // - if (value >= 0 && value <= 100)
    // This would require analyzing the actual usage in code
    return null;
  }
}

export async function analyzeCodebase(options: {
  tsConfigPath: string;
  stateFilePath?: string;
}): Promise<CodebaseAnalysis> {
  const extractor = new TypeExtractor(options.tsConfigPath);
  return extractor.analyzeCodebase(options.stateFilePath);
}
