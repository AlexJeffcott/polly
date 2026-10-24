// Type extraction from TypeScript, on the typescript-7 checker

import type { Node, SourceFile } from "typescript-7/ast";
import type { Type } from "typescript-7/async";
import {
  type AnalysisProgram,
  type AnalysisSession,
  nameOf,
  typeAlias,
  typeAliases,
  typeIs,
  typeLiteralValue,
  withAnalysisSession,
} from "../program";
import type { CodebaseAnalysis, FieldAnalysis, MessageHandler, TypeInfo } from "../types";
import { HandlerExtractor } from "./handlers";

/** A string-literal type's value, as a one-element list; empty for any other type. */
function stringLiteralValues(type: Type): string[] {
  const value = typeLiteralValue(type);
  return typeof value === "string" ? [value] : [];
}

/**
 * Reads state and message types from the checker.
 *
 * PARITY: union members come back in checker creation order
 * (`unionMembers`), and creation order depends on what the checker was
 * asked before. So the extractor runs on its own `openIsolated` program and
 * asks its questions one at a time, in the order ts-morph asked them
 * (depth first, no batching across siblings): a batched query can create a
 * sibling's literal types before a nested member's and reorder a union.
 */
export class TypeExtractor {
  private tsConfigPath: string;

  constructor(tsConfigPath: string) {
    this.tsConfigPath = tsConfigPath;
  }

  /**
   * Analyze the codebase and extract state types and message types. With a
   * `session`, the extractor opens an isolated program in it and the caller
   * keeps ownership; without one it opens and closes a session of its own.
   */
  async analyzeCodebase(
    stateFilePath?: string,
    session?: AnalysisSession
  ): Promise<CodebaseAnalysis> {
    // The type queries run on an isolated program (their union order follows
    // checker history); the handler extraction then runs on the session's
    // shared program for the resolved tsconfig.
    const read = async (from: AnalysisSession) => {
      const types = await this.readTypes(await from.openIsolated(this.tsConfigPath), stateFilePath);
      const handlerAnalysis = await this.extractHandlerAnalysis(types.tsConfigPath, from);
      return { ...types, handlerAnalysis };
    };
    const { stateType, messageTypes, handlerAnalysis } = session
      ? await read(session)
      : await withAnalysisSession(read);

    // Analyze fields
    const fields = stateType ? this.analyzeFields(stateType) : [];

    // Filter message types and handlers to only include valid TLA+ identifiers
    const validMessageTypes = this.filterAndLogMessageTypes(
      messageTypes,
      handlerAnalysis.messageTypes
    );
    const validHandlers = this.filterAndLogHandlers(handlerAnalysis.handlers);

    // Ensure handlers have all required properties
    // biome-ignore lint/suspicious/noExplicitAny: Mapping partial handler objects to complete MessageHandler interface
    const completeHandlers: MessageHandler[] = validHandlers.map((h: any) => ({
      messageType: h.messageType,
      node: h.node || "unknown",
      assignments: h.assignments || [],
      preconditions: h.preconditions || [],
      postconditions: h.postconditions || [],
      location: h.location,
      relationships: h.relationships,
      origin: h.origin,
    }));

    return {
      stateType,
      messageTypes: validMessageTypes,
      fields,
      handlers: completeHandlers,
      stateConstraints: handlerAnalysis.stateConstraints,
      globalStateConstraints: handlerAnalysis.globalStateConstraints,
      verifiedStates: handlerAnalysis.verifiedStates,
      meshOrPeerSignals: handlerAnalysis.meshOrPeerSignals,
      resources: handlerAnalysis.resources,
      offSurfaceMutations: handlerAnalysis.offSurfaceMutations,
    };
  }

  /** The state type, the message types and the resolved tsconfig path, read from the checker. */
  private async readTypes(
    program: AnalysisProgram,
    stateFilePath?: string
  ): Promise<{ stateType: TypeInfo | null; messageTypes: string[]; tsConfigPath: string }> {
    // Find state type
    const stateType = stateFilePath
      ? await this.extractStateType(program, stateFilePath)
      : await this.findStateType(program);

    // Find message types
    const messageTypes = await this.findMessageTypes(program);

    const configFilePath = program.compilerOptions.configFilePath;
    const tsConfigPath = typeof configFilePath === "string" ? configFilePath : "tsconfig.json";
    return { stateType, messageTypes, tsConfigPath };
  }

  /** Extract handler analysis from the project, on the resolved tsconfig path. */
  private extractHandlerAnalysis(tsConfigPath: string, session: AnalysisSession) {
    const handlerExtractor = new HandlerExtractor(tsConfigPath);
    return handlerExtractor.extractHandlers(session);
  }

  /**
   * Filter and log message types, keeping every type that can be represented
   * in TLA+ (polly#144). A message type is only ever emitted as a *quoted*
   * string literal ("POST /register/options") and turned into an action name
   * via sanitization, so non-identifier types like HTTP routes and
   * colon-namespaced WS messages are perfectly representable. We drop only the
   * genuinely unrepresentable ones — strings with no letter to anchor an action
   * name (empty, whitespace, all-symbol).
   */
  private filterAndLogMessageTypes(
    messageTypes: string[],
    handlerMessageTypes: Set<string>
  ): string[] {
    const allMessageTypes = Array.from(new Set([...messageTypes, ...handlerMessageTypes]));
    const keptMessageTypes: string[] = [];
    const droppedMessageTypes: string[] = [];

    for (const msgType of allMessageTypes) {
      if (this.canRepresentAsTLAAction(msgType)) {
        keptMessageTypes.push(msgType);
      } else {
        droppedMessageTypes.push(msgType);
      }
    }

    this.logDroppedMessageTypes(droppedMessageTypes);
    return keptMessageTypes;
  }

  /**
   * Log warnings about unrepresentable message types. Unlike the old
   * invalid-identifier path this is unconditional (not POLLY_DEBUG-gated):
   * silently dropping handlers was the core failure mode in polly#144.
   */
  private logDroppedMessageTypes(droppedMessageTypes: string[]): void {
    if (droppedMessageTypes.length === 0) return;

    console.log(
      `[WARN] Dropped ${droppedMessageTypes.length} unrepresentable message type(s) (no letter to form a TLA+ action name):`
    );
    for (const dropped of droppedMessageTypes) {
      console.log(`[WARN]   - "${dropped}"`);
    }
  }

  /**
   * Filter and log handlers, keeping every handler whose message type is
   * representable in TLA+ (polly#144 — HTTP routes and colon-namespaced
   * messages included).
   */
  private filterAndLogHandlers(
    handlers: Array<{ messageType: string; location: { file: string; line: number } }>
  ) {
    const keptHandlers = handlers.filter((h) => this.canRepresentAsTLAAction(h.messageType));

    this.logDroppedHandlers(handlers, keptHandlers);
    return keptHandlers;
  }

  /**
   * Log warnings about dropped handlers (unconditional — see polly#144).
   */
  private logDroppedHandlers(
    allHandlers: Array<{ messageType: string; location: { file: string; line: number } }>,
    keptHandlers: Array<{ messageType: string }>
  ): void {
    const droppedHandlerCount = allHandlers.length - keptHandlers.length;
    if (droppedHandlerCount === 0) return;

    console.log(
      `[WARN] Dropped ${droppedHandlerCount} handler(s) with unrepresentable message types:`
    );
    for (const handler of allHandlers) {
      if (!this.canRepresentAsTLAAction(handler.messageType)) {
        console.log(
          `[WARN]   - Handler for "${handler.messageType}" at ${handler.location.file}:${handler.location.line}`
        );
      }
    }
  }

  /**
   * Check whether a message type can be represented in the generated TLA+
   * (polly#144). The type itself becomes a quoted string literal, so the only
   * hard requirement is that it contains at least one letter — enough to
   * sanitize into a valid `Handle…` action name. Everything else (slashes,
   * colons, spaces, leading digits) is fine. Strings carrying TS
   * type-expression punctuation (`{}();<>=`) are rejected as extraction
   * artifacts rather than real message types.
   */
  private canRepresentAsTLAAction(s: string): boolean {
    return typeof s === "string" && /[a-zA-Z]/.test(s) && !/[{}();<>=]/.test(s);
  }

  /**
   * Extract state type from a specific file
   */
  private async extractStateType(
    program: AnalysisProgram,
    filePath: string
  ): Promise<TypeInfo | null> {
    const sourceFile = program.sourceFile(filePath);
    if (!sourceFile) {
      return null;
    }

    // Look for type alias named "AppState" or similar
    const alias =
      typeAlias(sourceFile, "AppState") ||
      typeAlias(sourceFile, "State") ||
      typeAliases(sourceFile)[0];

    if (!alias) {
      return null;
    }

    const type = await program.typeOf(alias);
    return this.convertType(program, type, nameOf(alias) ?? "");
  }

  /**
   * Find state type by searching common patterns
   */
  private async findStateType(program: AnalysisProgram): Promise<TypeInfo | null> {
    // Search for files with "state" in the name
    const stateFiles = program.sourceFilesMatching("**/state*.ts");

    for (const file of stateFiles) {
      const alias = typeAlias(file, "AppState") || typeAlias(file, "State");

      if (alias) {
        const type = await program.typeOf(alias);
        return this.convertType(program, type, nameOf(alias) ?? "");
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
   * - Mapped types
   */
  private async findMessageTypes(program: AnalysisProgram): Promise<string[]> {
    const messageTypes: string[] = [];
    const warnings: string[] = [];

    // Search for files with "message" in the name
    const messageFiles = program.sourceFilesMatching("**/message*.ts");

    for (const file of messageFiles) {
      // Look for type aliases that might contain message types
      for (const alias of typeAliases(file)) {
        const extractedTypes = await this.extractMessageTypesFromType(
          program,
          await program.typeOf(alias),
          nameOf(alias) ?? "",
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
   *
   * There is no conditional-type branch: the ts-morph version probed for an
   * `isConditionalType` method that ts-morph's Type did not have, so that
   * branch never ran, and a conditional type falls through to the text checks.
   */
  private async extractMessageTypesFromType(
    program: AnalysisProgram,
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    if (typeIs.union(type)) {
      return this.extractFromUnionType(program, type, typeName, sourceFile, warnings);
    }

    if (await type.getAliasSymbol()) {
      return this.extractFromTypeAlias(program, type, typeName, sourceFile, warnings);
    }

    const text = await program.typeText(type);

    if (text.includes("[K in ")) {
      return this.extractFromMappedType(program, text, sourceFile, warnings);
    }

    if (text.includes("`")) {
      this.warnTemplateLiteral(text, warnings);
      return [];
    }

    return [];
  }

  /**
   * Extract message types from union type
   */
  private async extractFromUnionType(
    program: AnalysisProgram,
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    const messageTypes: string[] = [];
    const unionTypes = await program.unionMembers(type);

    for (const unionType of unionTypes) {
      const extracted = await this.extractFromUnionMember(
        program,
        unionType,
        typeName,
        sourceFile,
        warnings
      );
      messageTypes.push(...extracted);
    }

    return messageTypes;
  }

  /**
   * Extract message types from a single union member
   */
  private async extractFromUnionMember(
    program: AnalysisProgram,
    unionType: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    if (typeIs.object(unionType)) {
      return this.extractFromDiscriminatedUnion(program, unionType, sourceFile, warnings);
    }

    if (typeIs.stringLiteral(unionType)) {
      return stringLiteralValues(unionType);
    }

    const aliasedType = await program.aliasDeclaredType(unionType);
    if (aliasedType) {
      return this.extractMessageTypesFromType(program, aliasedType, typeName, sourceFile, warnings);
    }

    return [];
  }

  /**
   * Extract message types from discriminated union
   */
  private async extractFromDiscriminatedUnion(
    program: AnalysisProgram,
    unionType: Type,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    const typeProperty = await program.property(unionType, "type", sourceFile);
    if (!typeProperty) {
      return [];
    }

    const typeType = typeProperty.type;

    if (typeIs.stringLiteral(typeType)) {
      return stringLiteralValues(typeType);
    }

    const text = await program.typeText(typeType);
    if (text.includes("`")) {
      warnings.push(`Template literal type in discriminant: ${text} - may be unbounded`);
    }

    return [];
  }

  /**
   * Extract message types from type alias
   */
  private async extractFromTypeAlias(
    program: AnalysisProgram,
    type: Type,
    typeName: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    const aliasedType = await program.aliasDeclaredType(type);
    // ts-morph cached one wrapper per checker type, so its `===` was type identity.
    if (!aliasedType || aliasedType.id === type.id) {
      return [];
    }

    return this.extractMessageTypesFromType(program, aliasedType, typeName, sourceFile, warnings);
  }

  /**
   * Extract message types from mapped type (`text` is the type's text)
   */
  private async extractFromMappedType(
    program: AnalysisProgram,
    text: string,
    sourceFile: SourceFile,
    warnings: string[]
  ): Promise<string[]> {
    warnings.push(`Mapped type detected: ${text} - attempting to extract keys`);

    const match = text.match(/\[K in ([^\]]+)\]/);
    if (!match?.[1]) {
      return [];
    }

    const keyTypeName = match[1].trim();
    const keyTypeAlias = typeAlias(sourceFile, keyTypeName);

    if (!keyTypeAlias) {
      return [];
    }

    const keyType = await program.typeOf(keyTypeAlias);
    return this.extractMessageTypesFromType(program, keyType, keyTypeName, sourceFile, warnings);
  }

  /**
   * Warn about template literal types (`text` is the type's text)
   */
  private warnTemplateLiteral(text: string, warnings: string[]): void {
    warnings.push(
      `Template literal type: ${text} - this creates an unbounded set and cannot be fully extracted`
    );
  }

  /**
   * Convert a checker Type to our TypeInfo
   */
  private async convertType(program: AnalysisProgram, type: Type, name: string): Promise<TypeInfo> {
    const nullable = await program.isNullable(type);

    if (typeIs.boolean(type) || typeIs.booleanLiteral(type)) {
      return { name, kind: "boolean", nullable };
    }

    if (typeIs.union(type)) {
      return this.convertUnionType(program, type, name, nullable);
    }

    if (typeIs.string(type) || typeIs.stringLiteral(type)) {
      return { name, kind: "string", nullable };
    }

    if (typeIs.number(type) || typeIs.numberLiteral(type)) {
      return { name, kind: "number", nullable };
    }

    const elementType = await program.arrayElement(type);
    if (elementType) {
      return {
        name,
        kind: "array",
        nullable,
        elementType: await this.convertType(program, elementType, `${name}_element`),
      };
    }

    const collectionType = await this.tryConvertCollectionType(program, type, name, nullable);
    if (collectionType) {
      return collectionType;
    }

    if (typeIs.object(type)) {
      return this.convertObjectType(program, type, name, nullable);
    }

    if (typeIs.null(type)) {
      return { name, kind: "null", nullable: true };
    }

    return { name, kind: "unknown", nullable };
  }

  /**
   * Convert union type to TypeInfo
   */
  private async convertUnionType(
    program: AnalysisProgram,
    type: Type,
    name: string,
    nullable: boolean
  ): Promise<TypeInfo> {
    const unionTypes = await program.unionMembers(type);

    // Check for string literal union (enum)
    const allStringLiterals = unionTypes.every((t) => typeIs.stringLiteral(t));
    if (allStringLiterals) {
      const enumValues = unionTypes.flatMap(stringLiteralValues);
      return { name, kind: "enum", nullable, enumValues };
    }

    // Check for nullable type (T | null | undefined)
    const nonNullTypes = unionTypes.filter((t) => !typeIs.null(t) && !typeIs.undefined(t));

    if (nonNullTypes.length === 1) {
      const firstType = nonNullTypes[0];
      if (firstType) {
        const baseType = await this.convertType(program, firstType, name);
        return { ...baseType, nullable: true };
      }
    }

    // Generic union
    const members: TypeInfo[] = [];
    for (const [i, t] of unionTypes.entries()) {
      members.push(await this.convertType(program, t, `${name}_${i}`));
    }
    return { name, kind: "union", nullable, unionTypes: members };
  }

  /**
   * Try to convert Map or Set type to TypeInfo
   */
  private async tryConvertCollectionType(
    program: AnalysisProgram,
    type: Type,
    name: string,
    nullable: boolean
  ): Promise<TypeInfo | null> {
    const symbol = await type.getSymbol();
    if (!symbol) return null;

    const symbolName = symbol.name;

    if (symbolName === "Map") {
      const valueArg = (await program.typeArguments(type))[1];
      return {
        name,
        kind: "map",
        nullable,
        valueType: valueArg
          ? await this.convertType(program, valueArg, `${name}_value`)
          : undefined,
      };
    }

    if (symbolName === "Set") {
      const elementArg = (await program.typeArguments(type))[0];
      return {
        name,
        kind: "set",
        nullable,
        elementType: elementArg
          ? await this.convertType(program, elementArg, `${name}_element`)
          : undefined,
      };
    }

    return null;
  }

  /**
   * Convert object type to TypeInfo
   */
  private async convertObjectType(
    program: AnalysisProgram,
    type: Type,
    name: string,
    nullable: boolean
  ): Promise<TypeInfo> {
    const properties: Record<string, TypeInfo> = {};
    const at: Node | undefined = program.sourceFiles[0];

    if (at) {
      for (const prop of await program.propertySymbols(type)) {
        const propType = await program.symbolTypeAt(prop, at);
        properties[prop.name] = await this.convertType(program, propType, prop.name);
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

/**
 * Analyze a codebase for `polly verify`. With `session`, the type queries
 * run on an isolated program in it and the caller closes it; without one the
 * call opens and closes a session of its own.
 */
export async function analyzeCodebase(options: {
  tsConfigPath: string;
  stateFilePath?: string;
  session?: AnalysisSession;
}): Promise<CodebaseAnalysis> {
  const extractor = new TypeExtractor(options.tsConfigPath);
  return extractor.analyzeCodebase(options.stateFilePath, options.session);
}
