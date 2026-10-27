// Handler extraction from TypeScript code
// Extracts message handlers and their state mutations
//
// STATE ASSIGNMENT EXTRACTION - SUPPORTED PATTERNS
//
// The following patterns are extracted and converted to TLA+ state transitions:
//
// OBJECTS:
//   ✓ state.field = value                    → direct assignment
//   ✓ signal.value.field = value             → signal nested field
//   ✓ signal.value = { field: value }        → object literal
//   ✓ signal.value = { ...signal.value, f }  → spread update (extracts changed fields)
//
// ARRAYS:
//   ✓ [...arr, item]                         → Append(@, payload)
//   ✓ [item, ...arr]                         → <<payload>> \o @
//   ✓ arr.filter(...)                        → SelectSeq(@, LAMBDA t: TRUE)
//   ✓ arr.map(...)                           → [i \in DOMAIN @ |-> @[i]]
//   ✓ arr.slice(...)                         → SubSeq(@, 1, Len(@))
//   ✓ arr.concat(...)                        → @ \o <<payload>>
//   ✓ arr.reverse()                          → [i \in DOMAIN @ |-> @[Len(@) - i + 1]]
//
// SETS:
//   ✓ new Set([...set, item])                → @ \union {payload}
//   ✓ new Set([...set].filter(...))          → @ \ {payload}
//   ✓ new Set()                              → {}
//
// MAPS:
//   ✓ new Map([...map, [k, v]])              → [@ EXCEPT ![payload.key] = payload.value]
//   ✓ new Map([...map].filter(...))          → [k \in DOMAIN @ \ {payload.key} |-> @[k]]
//   ✓ new Map()                              → <<>>
//
// UNSUPPORTED PATTERNS (will emit warnings)
//
// MUTATING METHODS (modify in place, don't return new value):
//   ✗ arr.push(), arr.pop(), arr.shift(), arr.unshift(), arr.splice()
//   ✗ arr.sort() with in-place mutation
//   ✗ set.add(), set.delete(), set.clear()
//   ✗ map.set(), map.delete(), map.clear()
//
// QUERY METHODS (return non-collection values):
//   ✗ arr.find(), arr.findIndex(), arr.reduce()
//   ✗ arr.some(), arr.every(), arr.includes(), arr.indexOf()
//   ✗ set.has(), map.has(), map.get()
//
// COMPLEX EXPRESSIONS:
//   ✗ Ternary expressions in assignments
//   ✗ Function calls as values (except supported collection methods)
//   ✗ Computed property names
//   ✗ Dynamic field names
//   ✗ Nested object updates beyond first level
//   ✗ Object.assign(), Object.keys(), Object.values(), Object.entries()
//
// To request support for additional patterns, please open an issue at:
// https://github.com/anthropics/polly/issues

import { basename } from "node:path";
import type {
  ArrayLiteralExpression,
  ArrowFunction,
  BinaryExpression,
  CallExpression,
  Declaration,
  Expression,
  FunctionDeclaration,
  FunctionExpression,
  Identifier,
  IfStatement,
  MethodDeclaration,
  NewExpression,
  Node,
  ObjectLiteralExpression,
  PropertyAccessExpression,
  SourceFile,
  Statement,
  SwitchStatement,
  VariableDeclaration,
} from "typescript-7/ast";
import { SyntaxKind } from "typescript-7/ast";
import {
  isArrayLiteralExpression,
  isArrowFunction,
  isAwaitExpression,
  isBinaryExpression,
  isBlock,
  isCallExpression,
  isCaseClause,
  isClassDeclaration,
  isConditionalExpression,
  isElementAccessExpression,
  isExpressionStatement,
  isFunctionDeclaration,
  isFunctionExpression,
  isGetAccessorDeclaration,
  isIdentifier,
  isIfStatement,
  isMethodDeclaration,
  isNewExpression,
  isNumericLiteral,
  isObjectLiteralExpression,
  isParenthesizedExpression,
  isPostfixUnaryExpression,
  isPrefixUnaryExpression,
  isPropertyAccessExpression,
  isPropertyAssignment,
  isReturnStatement,
  isSetAccessorDeclaration,
  isShorthandPropertyAssignment,
  isSpreadAssignment,
  isSpreadElement,
  isStringLiteral,
  isSwitchStatement,
  isTemplateExpression,
  isTypePredicateNode,
  isVariableDeclaration,
  isVariableDeclarationList,
} from "typescript-7/ast/is";
import {
  type AnalysisProgram,
  type AnalysisSource,
  declarationKind,
  firstAncestor,
  firstDescendant,
  forEachDescendant,
  functionDeclarations,
  hasExportKeyword,
  importDeclarations,
  kindName,
  lineAndColumn,
  literalValue,
  moduleSpecifierValue,
  nameOf,
  objectProperty,
  startLine,
  startLinePos,
  startOf,
  textOf,
  variableStatements,
  withProgram,
} from "../program";
import type {
  ComponentRelationship,
  GlobalStateConstraint,
  MeshOrPeerSignalInfo,
  MessageHandler,
  OffSurfaceMutation,
  ResourceInfo,
  StateAssignment,
  StateConstraint,
  VerificationCondition,
  VerifiedStateInfo,
} from "../types";
import { RelationshipExtractor } from "./relationships";
import { isOffSurfacePath } from "./source-surface";

/** A function whose parameters and body a handler is extracted from. */
type HandlerFunction = ArrowFunction | FunctionExpression | FunctionDeclaration | MethodDeclaration;

export interface ExtractionWarning {
  type: "unsupported_pattern";
  pattern: string;
  location: string;
  suggestion: string;
}

export interface HandlerAnalysis {
  handlers: MessageHandler[];
  messageTypes: Set<string>;
  stateConstraints: StateConstraint[];
  globalStateConstraints: GlobalStateConstraint[];
  verifiedStates: VerifiedStateInfo[];
  meshOrPeerSignals: MeshOrPeerSignalInfo[];
  resources: ResourceInfo[];
  offSurfaceMutations: OffSurfaceMutation[];
  warnings: ExtractionWarning[];
}

/** ts-morph `getName()` on a node whose name is required (property access, variable, property, parameter). */
function nameText(node: Node & { readonly name: Node }): string {
  return textOf(node.name);
}

/** ts-morph `getArguments()`: a `new X` without parentheses has none. */
function argumentsOf(expr: CallExpression | NewExpression): readonly Expression[] {
  return expr.arguments ?? [];
}

/**
 * Extracts message handlers and their state mutations from one tsconfig's
 * program. AST-only apart from go-to-definition (three lookups, answered from
 * `prefetchDefinitions`), import targets (`prefetchImports`) and the
 * `isExported` check of the issue-#27 lift pass.
 */
export class HandlerExtractor {
  private tsConfigPath: string;
  private programRef: AnalysisProgram | undefined;
  private relationshipRef: RelationshipExtractor | undefined;
  private typeGuardCache: WeakMap<SourceFile, Map<string, string>>;
  private analyzedFiles: Set<string>; // Track files we've already analyzed
  private packageRoot: string; // Package directory (contains package.json)
  private warnings: ExtractionWarning[]; // Warnings for unsupported patterns
  private currentFunctionParams: string[] = []; // Current handler's parameter names
  private contextOverrides: Map<string, string>; // path prefix → context name
  // polly#163: source spans of every function body the extractor modelled as a
  // handler. A verified-state write outside all of these is "off-surface".
  private onSurfaceSpans: Array<{ file: string; start: number; end: number }> = [];
  // Definition lookups the prefetch did not cover (see `definitionsOf`).
  private prefetchMisses: string[] = [];

  constructor(tsConfigPath: string, contextOverrides?: Map<string, string>) {
    this.tsConfigPath = tsConfigPath;
    this.typeGuardCache = new WeakMap();
    this.analyzedFiles = new Set<string>();
    this.warnings = [];
    this.contextOverrides = contextOverrides || new Map();
    // Find package root by looking for package.json from tsconfig location
    this.packageRoot = this.findPackageRoot(tsConfigPath);
  }

  /** The program of the running `extractHandlers` call. */
  private get program(): AnalysisProgram {
    if (!this.programRef) throw new Error("HandlerExtractor: no extraction is running");
    return this.programRef;
  }

  private get relationshipExtractor(): RelationshipExtractor {
    if (!this.relationshipRef) throw new Error("HandlerExtractor: no extraction is running");
    return this.relationshipRef;
  }

  /**
   * ts-morph `identifier.getDefinitionNodes()`, answered from the prefetch.
   *
   * Every identifier this extractor resolves is a call callee, a call or
   * `new` argument, or a property-assignment value, which is the set the
   * default `prefetchDefinitions()` covers. The call sites swallow errors
   * (ts-morph's lookup could throw), so a lookup outside the prefetch would
   * silently lose a handler; it is recorded instead, and `extractHandlers`
   * throws on it.
   */
  private definitionsOf(identifier: Identifier): readonly Declaration[] {
    try {
      return this.program.definitionNodes(identifier);
    } catch (error) {
      this.prefetchMisses.push(error instanceof Error ? error.message : String(error));
      return [];
    }
  }

  /**
   * Emit a warning for an unsupported pattern
   */
  private warnUnsupportedPattern(pattern: string, location: string, suggestion: string): void {
    // Deduplicate warnings by pattern + location
    const exists = this.warnings.some((w) => w.pattern === pattern && w.location === location);
    if (!exists) {
      this.warnings.push({
        type: "unsupported_pattern",
        pattern,
        location,
        suggestion,
      });
    }
  }

  /**
   * Extract parameter names from a function
   */
  private extractParameterNames(func: HandlerFunction): string[] {
    return func.parameters.map((p) => nameText(p));
  }

  /**
   * Get a location string for a node
   */
  private getNodeLocation(node: Node): string {
    const sourceFile = node.getSourceFile();
    const lineAndCol = lineAndColumn(sourceFile, startOf(node, sourceFile));
    const filePath = sourceFile.fileName;
    const relativePath = filePath.startsWith(this.packageRoot)
      ? filePath.substring(this.packageRoot.length + 1)
      : filePath;
    return `${relativePath}:${lineAndCol.line}`;
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
  //
  // With no `source`, opens (and closes) a session of its own; a passed
  // source stays the caller's.
  async extractHandlers(source?: AnalysisSource): Promise<HandlerAnalysis> {
    return withProgram(this.tsConfigPath, source, async (program) => {
      await Promise.all([program.prefetchDefinitions(), program.prefetchImports()]);
      this.programRef = program;
      this.relationshipRef = new RelationshipExtractor(program);
      this.prefetchMisses = [];
      try {
        const analysis = await this.extractFrom(program);
        if (this.prefetchMisses.length > 0) {
          throw new Error(
            `HandlerExtractor: ${this.prefetchMisses.length} definition lookup(s) outside the prefetch:\n${this.prefetchMisses.join("\n")}`
          );
        }
        return analysis;
      } finally {
        this.programRef = undefined;
        this.relationshipRef = undefined;
      }
    });
  }

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Handler extraction requires analyzing multiple patterns and file boundaries
  private async extractFrom(program: AnalysisProgram): Promise<HandlerAnalysis> {
    const handlers: MessageHandler[] = [];
    const messageTypes = new Set<string>();
    const invalidMessageTypes = new Set<string>();
    const stateConstraints: StateConstraint[] = [];
    const globalStateConstraints: GlobalStateConstraint[] = [];
    const verifiedStates: VerifiedStateInfo[] = [];
    const meshOrPeerSignals: MeshOrPeerSignalInfo[] = [];
    const resources: ResourceInfo[] = [];
    this.warnings = []; // Clear warnings from previous runs
    this.onSurfaceSpans = []; // polly#163: reset modelled-handler spans

    // Find all source files from tsconfig as potential entry points
    const allSourceFiles = program.sourceFiles;
    // Filter to only files within the package boundary
    const entryPoints = allSourceFiles.filter((f) => this.isWithinPackage(f.fileName));

    this.debugLogSourceFiles(allSourceFiles, entryPoints);

    // Analyze each entry point and follow its imports transitively
    for (const entryPoint of entryPoints) {
      this.analyzeFileAndImports(
        entryPoint,
        handlers,
        messageTypes,
        invalidMessageTypes,
        stateConstraints,
        globalStateConstraints,
        verifiedStates,
        resources
      );
    }

    // Issue #27: Second pass - find functions that modify verified states
    if (verifiedStates.length > 0) {
      if (process.env["POLLY_DEBUG"]) {
        console.log(
          `[DEBUG] Found ${verifiedStates.length} verified state(s), scanning for mutating functions...`
        );
      }

      for (const filePath of this.analyzedFiles) {
        const sourceFile = program.sourceFile(filePath);
        if (!sourceFile) continue;

        const mutatingHandlers = await this.findStateMutatingFunctions(sourceFile, verifiedStates);

        for (const handler of mutatingHandlers) {
          // Avoid duplicates - check if handler already exists for this message type
          const exists = handlers.some(
            (h) =>
              h.messageType === handler.messageType && h.location.file === handler.location.file
          );

          if (!exists) {
            handlers.push(handler);
            if (this.canRepresentAsTLAAction(handler.messageType)) {
              messageTypes.add(handler.messageType);
            } else {
              invalidMessageTypes.add(handler.messageType);
            }
          }
        }
      }
    }

    // polly#117: collect mesh- and peer-scoped signal declarations so
    // the CLI can warn when a requires/ensures predicate references
    // one — the verifier currently has no native support for their
    // cross-peer semantics.
    for (const filePath of this.analyzedFiles) {
      const sourceFile = program.sourceFile(filePath);
      if (!sourceFile) continue;
      meshOrPeerSignals.push(...this.extractMeshOrPeerSignalsFromFile(sourceFile));
    }

    // polly#163: third pass — find state-signal writes that fall outside every
    // function body the handler extraction above modelled (the non-dispatched
    // `register()` shape #160). Runs last so all on-surface spans are recorded.
    //
    // Scope is the whole state-signal family (config-free), not just
    // `{ verify: true }` declarations — dispatch handlers already pick up any
    // `signal.value` write by pattern, so the off-surface scan must too. The
    // verify layer (which has the config) separates declared fields from the
    // rest.
    const stateSignalNames = new Set<string>();
    for (const filePath of this.analyzedFiles) {
      const sourceFile = program.sourceFile(filePath);
      if (!sourceFile) continue;
      for (const name of this.extractStateSignalVariableNames(sourceFile)) {
        stateSignalNames.add(name);
      }
    }
    for (const v of verifiedStates) stateSignalNames.add(v.variableName);
    for (const m of meshOrPeerSignals) stateSignalNames.add(m.variableName);

    const offSurfaceMutations: OffSurfaceMutation[] = [];
    if (stateSignalNames.size > 0) {
      for (const filePath of this.analyzedFiles) {
        // Test/spec/feature files seed verified state directly by design; that
        // is not a model gap, so the off-surface scan only covers app source.
        if (!this.isOffSurfaceScannable(filePath)) continue;
        const sourceFile = program.sourceFile(filePath);
        if (!sourceFile) continue;
        offSurfaceMutations.push(...this.findOffSurfaceMutations(sourceFile, stateSignalNames));
      }
    }

    this.debugLogExtractionResults(handlers.length, invalidMessageTypes.size);
    this.debugLogAnalysisStats(allSourceFiles.length, entryPoints.length);

    return {
      handlers,
      messageTypes,
      stateConstraints,
      globalStateConstraints,
      verifiedStates,
      meshOrPeerSignals,
      resources,
      offSurfaceMutations,
      warnings: this.warnings,
    };
  }

  /**
   * Walk a source file for `$meshState(id, init)` and `$peerState(id, init)`
   * calls and return one entry per call, tagged with its scope.
   */
  extractMeshOrPeerSignalsFromFile(sourceFile: SourceFile): MeshOrPeerSignalInfo[] {
    const out: MeshOrPeerSignalInfo[] = [];
    const filePath = sourceFile.fileName;
    forEachDescendant(sourceFile, (node) => {
      const info = this.recognizeMeshOrPeerStateCall(node, filePath);
      if (info) out.push(info);
    });
    return out;
  }

  /**
   * Recognize a `$meshState(...)` or `$peerState(...)` call and return
   * a descriptor for the resulting signal. Mirrors
   * `recognizeVerifiedStateCall` but for the mesh/peer family.
   */
  private recognizeMeshOrPeerStateCall(node: Node, filePath: string): MeshOrPeerSignalInfo | null {
    if (!isCallExpression(node)) return null;
    const expression = node.expression;
    if (!isIdentifier(expression)) return null;

    const funcName = textOf(expression);
    const kind: "mesh" | "peer" | null =
      funcName === "$meshState" ? "mesh" : funcName === "$peerState" ? "peer" : null;
    if (!kind) return null;

    const args = node.arguments;
    const keyArg = args[0];
    if (!keyArg || !isStringLiteral(keyArg)) return null;
    const key = keyArg.text;

    const variableName = this.getVariableNameFromParent(node) || key;
    const access = this.extractMeshAccess(args[2]);

    return {
      kind,
      key,
      variableName,
      filePath,
      line: startLine(node),
      ...(access ? { access } : {}),
    };
  }

  /**
   * polly#114: pull the read/write predicate source text out of a
   * `$meshState` / `$peerState` declaration's `access` option. The
   * runtime access set cannot be resolved statically; the predicate
   * expression that gates it can, and is what the visualiser labels.
   */
  private extractMeshAccess(
    optionsArg: Node | undefined
  ): { read: string; write: string } | undefined {
    if (!optionsArg || !isObjectLiteralExpression(optionsArg)) return undefined;
    const accessProp = objectProperty(optionsArg, "access");
    if (!accessProp || !isPropertyAssignment(accessProp)) return undefined;
    const accessObj = accessProp.initializer;
    if (!accessObj || !isObjectLiteralExpression(accessObj)) return undefined;

    const predicateText = (name: string): string | undefined => {
      const prop = objectProperty(accessObj, name);
      if (!prop || !isPropertyAssignment(prop)) return undefined;
      return textOf(prop.initializer).replace(/\s+/g, " ").trim();
    };
    const read = predicateText("read");
    const write = predicateText("write");
    if (read === undefined && write === undefined) return undefined;
    return { read: read ?? "unset", write: write ?? "unset" };
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
    stateConstraints: StateConstraint[],
    globalStateConstraints: GlobalStateConstraint[],
    verifiedStates: VerifiedStateInfo[],
    resources: ResourceInfo[]
  ): void {
    const filePath = sourceFile.fileName;

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

    // Extract global state constraints (stateConstraint() calls)
    const fileGlobalConstraints = this.extractGlobalStateConstraintsFromFile(sourceFile);
    globalStateConstraints.push(...fileGlobalConstraints);

    // Issue #27: Extract verified states from this file
    const fileVerifiedStates = this.extractVerifiedStatesFromFile(sourceFile);
    verifiedStates.push(...fileVerifiedStates);

    // Extract $resource() calls and emit synthetic handlers
    const fileResources = this.extractResourcesFromFile(sourceFile, filePath);
    for (const resource of fileResources) {
      resources.push(resource);
      const context = this.inferContext(filePath);
      const syntheticHandlers = this.createResourceHandlers(resource, context);
      for (const handler of syntheticHandlers) {
        handlers.push(handler);
        if (this.canRepresentAsTLAAction(handler.messageType)) {
          messageTypes.add(handler.messageType);
        } else {
          invalidMessageTypes.add(handler.messageType);
        }
      }
    }

    // Follow imports to discover more files (within package boundary only)
    for (const importDecl of importDeclarations(sourceFile)) {
      const importedFile = this.program.moduleSpecifierSourceFile(importDecl);

      if (importedFile) {
        const importedPath = importedFile.fileName;

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
          stateConstraints,
          globalStateConstraints,
          verifiedStates,
          resources
        );
      } else if (process.env["POLLY_DEBUG"]) {
        // Log unresolved imports for debugging
        const specifier = moduleSpecifierValue(importDecl) ?? "";
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

  private debugLogSourceFiles(
    allSourceFiles: readonly SourceFile[],
    entryPoints: readonly SourceFile[]
  ): void {
    if (!process.env["POLLY_DEBUG"]) return;

    console.log(`[DEBUG] Loaded ${allSourceFiles.length} source files from tsconfig`);
    console.log(`[DEBUG] Filtered to ${entryPoints.length} entry points within package`);
    if (entryPoints.length <= 20) {
      for (const sf of entryPoints) {
        console.log(`[DEBUG]   - ${sf.fileName}`);
      }
    }
  }

  private categorizeHandlerMessageTypes(
    handlers: MessageHandler[],
    messageTypes: Set<string>,
    invalidMessageTypes: Set<string>
  ): void {
    for (const handler of handlers) {
      if (this.canRepresentAsTLAAction(handler.messageType)) {
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
   * Check whether a message type can be represented in the generated TLA+
   * (polly#144). Message types become quoted string literals and are sanitized
   * into `Handle…` action names, so HTTP routes ("POST /register/options") and
   * colon-namespaced messages ("chat:send") are all representable — the only
   * requirement is at least one letter to anchor the action name. Strings
   * carrying TS type-expression punctuation (`{}();<>=`) are rejected as
   * extraction artifacts rather than real message types.
   */
  private canRepresentAsTLAAction(s: string): boolean {
    return typeof s === "string" && /[a-zA-Z]/.test(s) && !/[{}();<>=]/.test(s);
  }

  /**
   * Extract handlers from a single source file
   */
  private extractFromFile(sourceFile: SourceFile): MessageHandler[] {
    const handlers: MessageHandler[] = [];
    const filePath = sourceFile.fileName;
    const context = this.inferContext(filePath);

    forEachDescendant(sourceFile, (node) => {
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
    if (isCallExpression(node)) {
      this.processCallExpressionHandler(node, context, filePath, handlers);
    }

    if (isSwitchStatement(node)) {
      const switchHandlers = this.extractSwitchCaseHandlers(node, context, filePath);
      handlers.push(...switchHandlers);
    }

    if (isVariableDeclaration(node)) {
      const mapHandlers = this.extractHandlerMapPattern(node, context, filePath);
      handlers.push(...mapHandlers);
    }

    if (isIfStatement(node) && !this.isElseIfStatement(node)) {
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
    const expression = node.expression;

    if (isPropertyAccessExpression(expression)) {
      const methodName = nameText(expression);

      if (methodName === "on" || methodName === "addEventListener") {
        const handler = this.extractHandler(node, context, filePath);
        if (handler) {
          handlers.push(handler);
        }
      }

      if (methodName === "ws") {
        this.extractElysiaWsHandlers(node, context, filePath, handlers);
      }

      // REST route handlers
      if (this.isRestMethod(methodName) && this.isWebFrameworkFile(node.getSourceFile())) {
        const restHandler = this.extractRestHandler(node, methodName, context, filePath);
        if (restHandler) {
          handlers.push(restHandler);
        }
      }
    }
  }

  /**
   * Check if a method name is a REST HTTP method
   */
  private isRestMethod(name: string): boolean {
    return ["get", "post", "put", "delete", "patch"].includes(name);
  }

  /**
   * Check if a node is an else-if statement
   */
  private isElseIfStatement(node: Node): boolean {
    const parent = node.parent;
    return parent !== undefined && isIfStatement(parent);
  }

  /**
   * Extract handler details from a .on() call expression
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: handler extraction requires branching logic
  private extractHandler(
    callExpr: CallExpression,
    context: string,
    filePath: string
  ): MessageHandler | null {
    const args = callExpr.arguments;

    if (args.length < 2) {
      return null;
    }

    // First argument should be the message type (string literal)
    const messageTypeArg = args[0];
    let messageType: string | null = null;

    if (messageTypeArg && isStringLiteral(messageTypeArg)) {
      messageType = messageTypeArg.text;
    } else if (messageTypeArg && isTemplateExpression(messageTypeArg)) {
      // Handle template literals if needed
      messageType = textOf(messageTypeArg).replace(/[`'"]/g, "");
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
    let actualHandler: ArrowFunction | FunctionExpression | FunctionDeclaration | null = null;

    if (handlerArg && (isArrowFunction(handlerArg) || isFunctionExpression(handlerArg))) {
      actualHandler = handlerArg;
    } else if (handlerArg && isIdentifier(handlerArg)) {
      // Resolve function reference (e.g., bus.on('query', handleQuery))
      actualHandler = this.resolveFunctionReference(handlerArg);
    }

    let parameters: string[] | undefined;

    if (actualHandler) {
      this.currentFunctionParams = this.extractParameterNames(actualHandler);
      parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.extractAssignments(actualHandler, assignments);
      this.extractVerificationConditions(actualHandler, preconditions, postconditions);

      // Check for async mutations (potential race conditions)
      if (isArrowFunction(actualHandler) || isFunctionExpression(actualHandler)) {
        this.checkAsyncMutations(actualHandler, messageType);
      }
      this.currentFunctionParams = [];
    }

    const line = startLine(callExpr);

    // Extract relationships from handler code
    const sourceFile = callExpr.getSourceFile();
    const handlerName = `${messageType}_handler`;
    let relationships: ComponentRelationship[] | undefined;

    if (actualHandler) {
      const detectedRelationships = this.relationshipExtractor.extractFromHandler(
        actualHandler,
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
      origin: "event" as const,
      parameters,
    };
  }

  /**
   * Extract handlers from Elysia .ws() call
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: WebSocket handler extraction requires analyzing multiple callback patterns
  private extractElysiaWsHandlers(
    node: CallExpression,
    context: string,
    filePath: string,
    handlers: MessageHandler[]
  ): void {
    const args = node.arguments;
    if (args.length < 2) return;

    // First arg is the route path (string)
    const routeArg = args[0];
    if (!routeArg || !isStringLiteral(routeArg)) return;
    const routePath = routeArg.text;

    // Second arg is the config object
    const configArg = args[1];
    if (!configArg || !isObjectLiteralExpression(configArg)) return;

    // Look for message, open, close callbacks
    const callbacks = ["message", "open", "close"];
    for (const cbName of callbacks) {
      const prop = objectProperty(configArg, cbName);
      if (!prop) continue;

      let funcBody: HandlerFunction | null = null;

      if (isMethodDeclaration(prop)) {
        // Method shorthand: message(ws, data) { ... }
        // Use the method body directly for analysis
        funcBody = prop;
      } else if (isPropertyAssignment(prop)) {
        const init = prop.initializer;
        if (init && (isArrowFunction(init) || isFunctionExpression(init))) {
          funcBody = init;
        }
      }

      if (!funcBody) continue;

      if (cbName === "message") {
        // Walk body for type guard handlers and switch statements
        const body = funcBody.body;
        if (!body) continue;

        const subHandlers = this.extractSubHandlersFromBody(body, context, filePath);

        if (subHandlers.length > 0) {
          handlers.push(...subHandlers);
        } else {
          // No sub-handlers found, register as a generic ws message handler
          handlers.push(
            this.buildWsHandler(
              `ws_message`,
              routePath,
              context,
              filePath,
              funcBody,
              startLine(node)
            )
          );
        }
      } else {
        // open/close lifecycle handlers
        handlers.push(
          this.buildWsHandler(
            `ws_${cbName}`,
            routePath,
            context,
            filePath,
            funcBody,
            startLine(node)
          )
        );
      }
    }
  }

  /**
   * Extract sub-handlers (type guards and switch cases) from a function body
   */
  private extractSubHandlersFromBody(
    body: Node,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const subHandlers: MessageHandler[] = [];

    forEachDescendant(body, (child) => {
      if (isIfStatement(child) && !this.isElseIfStatement(child)) {
        const typeGuardHandlers = this.extractTypeGuardHandlers(child, context, filePath);
        subHandlers.push(...typeGuardHandlers);
      }
      if (isSwitchStatement(child)) {
        const switchHandlers = this.extractSwitchCaseHandlers(child, context, filePath);
        subHandlers.push(...switchHandlers);
      }
    });

    return subHandlers;
  }

  /**
   * Build a WebSocket handler entry
   */
  private buildWsHandler(
    messageType: string,
    _routePath: string,
    context: string,
    filePath: string,
    funcBody: HandlerFunction,
    line: number
  ): MessageHandler {
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    this.currentFunctionParams = this.extractParameterNames(funcBody);
    this.extractAssignments(funcBody, assignments);
    this.extractVerificationConditions(funcBody, preconditions, postconditions);
    this.currentFunctionParams = [];

    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: { file: filePath, line },
      origin: "event" as const,
    };
  }

  /**
   * Extract a REST route handler (.get/.post/.put/.delete/.patch)
   */
  private extractRestHandler(
    node: CallExpression,
    methodName: string,
    context: string,
    filePath: string
  ): MessageHandler | null {
    const args = node.arguments;
    if (args.length < 2) return null;

    // First arg must be a string literal route path
    const routeArg = args[0];
    if (!routeArg || !isStringLiteral(routeArg)) return null;
    const routePath = routeArg.text;

    const httpMethod = methodName.toUpperCase();
    const messageType = `${httpMethod} ${routePath}`;

    // Second arg is the handler function
    const handlerArg = args[1];
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    let actualHandler: ArrowFunction | FunctionExpression | FunctionDeclaration | null = null;

    if (handlerArg && (isArrowFunction(handlerArg) || isFunctionExpression(handlerArg))) {
      actualHandler = handlerArg;
    } else if (handlerArg && isIdentifier(handlerArg)) {
      actualHandler = this.resolveFunctionReference(handlerArg);
    }

    let parameters: string[] | undefined;

    if (actualHandler) {
      this.currentFunctionParams = this.extractParameterNames(actualHandler);
      parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.extractAssignments(actualHandler, assignments);
      this.extractVerificationConditions(actualHandler, preconditions, postconditions);
      this.currentFunctionParams = [];
    }

    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: {
        file: filePath,
        line: startLine(node),
      },
      origin: "event" as const,
      parameters,
      handlerKind: "rest",
      httpMethod,
      routePath,
    };
  }

  /**
   * Check if a source file imports from a known web framework
   */
  private isWebFrameworkFile(sourceFile: SourceFile): boolean {
    const frameworks = ["elysia", "express", "hono", "fastify", "koa", "@elysiajs/eden"];
    for (const importDecl of importDeclarations(sourceFile)) {
      const specifier = moduleSpecifierValue(importDecl) ?? "";
      if (frameworks.some((fw) => specifier === fw || specifier.startsWith(`${fw}/`))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Extract state assignments from a handler function
   * Handles:
   * - Simple assignments: state.field = value
   * - Compound operators: state.count += 1
   * - Unary operators: state.count++, state.count--, ++state.count, --state.count
   * - Array mutations: state.items.push(item)
   * - Array indexing: state.items[0] = value
   */
  private extractAssignments(funcNode: HandlerFunction, assignments: StateAssignment[]): void {
    // polly#163: this body is part of the modelled handler surface. Any
    // verified-state write inside its span is "on-surface" and must not be
    // re-reported as an escaped mutator.
    this.recordOnSurfaceSpan(funcNode);
    forEachDescendant(funcNode, (node: Node) => {
      if (isBinaryExpression(node)) {
        this.extractBinaryExpressionAssignment(node, assignments);
      }

      if (isCallExpression(node)) {
        this.extractArrayMutationAssignment(node, assignments);
      }

      if (isPostfixUnaryExpression(node) || isPrefixUnaryExpression(node)) {
        this.extractUnaryExpressionAssignment(node, assignments);
      }
    });
  }

  /**
   * Extract assignments from binary expressions (=, +=, -=, etc.)
   */
  private extractBinaryExpressionAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!isBinaryExpression(node)) return;

    const operator = textOf(node.operatorToken);

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
    if (!isBinaryExpression(node)) return;

    const left = node.left;
    const right = node.right;

    if (isPropertyAccessExpression(left)) {
      this.extractPropertyAccessAssignment(left, right, assignments);
    } else if (isElementAccessExpression(left)) {
      this.extractElementAccessAssignment(left, right, assignments);
    }
  }

  /**
   * Extract property access assignment (state.field = value or someState.value.field = value)
   */
  private extractPropertyAccessAssignment(
    left: Node,
    right: Node,
    assignments: StateAssignment[]
  ): void {
    if (!isPropertyAccessExpression(left)) return;

    const fieldPath = this.getPropertyPath(left);

    // Try each pattern in order
    if (this.tryExtractStateFieldPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalNestedFieldPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalObjectPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalArrayPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSignalMethodPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractSetConstructorPattern(fieldPath, right, assignments)) return;
    if (this.tryExtractMapConstructorPattern(fieldPath, right, assignments)) return;
    this.tryExtractSignalDirectValuePattern(fieldPath, right, assignments);
  }

  /** Pattern 1: state.field = value */
  private tryExtractStateFieldPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.startsWith("state.")) return false;
    const field = fieldPath.substring(6);
    const value = this.extractValue(right);
    if (value !== undefined) {
      assignments.push({ field, value });
    }
    return true;
  }

  /** Pattern 2: someState.value.field = value (signal pattern with nested field) */
  private tryExtractSignalNestedFieldPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    const valueFieldMatch = fieldPath.match(/^([a-zA-Z_][a-zA-Z0-9_]*)\.value\.(.+)$/);
    if (!valueFieldMatch?.[1] || !valueFieldMatch?.[2]) return false;
    const signalName = valueFieldMatch[1];
    const fieldName = valueFieldMatch[2];
    const value = this.extractValue(right);
    if (value !== undefined) {
      assignments.push({ field: `${signalName}_${fieldName}`, value });
    }
    return true;
  }

  /** Pattern 3: someState.value = { object literal } (signal replacement or spread update) */
  private tryExtractSignalObjectPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !isObjectLiteralExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);
    if (this.isSpreadUpdatePattern(right, fieldPath)) {
      this.extractSpreadUpdateAssignments(right, assignments, signalName);
    } else {
      this.extractObjectLiteralAssignments(right, assignments, signalName);
    }
    return true;
  }

  /** Check if object literal is a spread update pattern: { ...existing, field: value } */
  private isSpreadUpdatePattern(
    objectLiteral: ObjectLiteralExpression,
    fieldPath: string
  ): boolean {
    const properties = objectLiteral.properties;
    if (properties.length === 0) return false;
    const firstProp = properties[0];
    if (!firstProp || !isSpreadAssignment(firstProp)) return false;
    const spreadExpr = firstProp.expression;
    if (!spreadExpr) return false;
    return this.getPropertyPath(spreadExpr) === fieldPath;
  }

  /** Pattern 4: someState.value = [...someState.value, item] (array spread) */
  private tryExtractSignalArrayPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !isArrayLiteralExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);
    const arrayAssignment = this.extractArraySpreadOperation(right, fieldPath, signalName);
    if (arrayAssignment) {
      assignments.push(arrayAssignment);
    }
    return true;
  }

  /** Pattern 5: someState.value = someState.value.filter(...) or .map(...) (array methods) */
  private tryExtractSignalMethodPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !isCallExpression(right)) return false;
    const signalName = fieldPath.slice(0, -6);

    // Check for and warn about Set/Map direct method calls that mutate
    this.checkForMutatingCollectionMethods(right);

    const methodAssignment = this.extractArrayMethodOperation(right, fieldPath, signalName);
    if (methodAssignment) {
      assignments.push(methodAssignment);
    }
    return true;
  }

  /** Check for mutating Set/Map methods and emit warnings */
  private checkForMutatingCollectionMethods(callExpr: CallExpression): void {
    const expression = callExpr.expression;
    if (!isPropertyAccessExpression(expression)) return;

    const methodName = nameText(expression);
    const sourceExpr = expression.expression;

    // Check for Set mutating methods
    const setMethods = ["add", "delete", "clear"];
    if (setMethods.includes(methodName)) {
      // Try to determine if this is a Set operation by checking the source expression
      const sourceText = textOf(sourceExpr);
      if (sourceText.includes("Set") || this.looksLikeSetOrMap(sourceExpr, "Set")) {
        this.warnUnsupportedPattern(
          `set.${methodName}()`,
          this.getNodeLocation(callExpr),
          `Set.${methodName}() mutates in place. Use: new Set([...set, item]) for add, new Set([...set].filter(...)) for delete.`
        );
      }
    }

    // Check for Map mutating methods
    const mapMethods = ["set", "delete", "clear"];
    if (mapMethods.includes(methodName)) {
      const sourceText = textOf(sourceExpr);
      if (sourceText.includes("Map") || this.looksLikeSetOrMap(sourceExpr, "Map")) {
        this.warnUnsupportedPattern(
          `map.${methodName}()`,
          this.getNodeLocation(callExpr),
          `Map.${methodName}() mutates in place. Use: new Map([...map, [key, value]]) for set, new Map([...map].filter(...)) for delete.`
        );
      }
    }
  }

  /** Heuristic check if an expression might be a Set or Map */
  private looksLikeSetOrMap(expr: Node, collectionType: "Set" | "Map"): boolean {
    const text = textOf(expr).toLowerCase();
    return text.includes(collectionType.toLowerCase());
  }

  /** Pattern 6: someState.value = new Set([...someState.value, item]) (Set operations) */
  private tryExtractSetConstructorPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !isNewExpression(right)) return false;
    const constructorExpr = right.expression;
    if (!isIdentifier(constructorExpr) || textOf(constructorExpr) !== "Set") return false;

    const signalName = fieldPath.slice(0, -6);
    const setAssignment = this.extractSetOperation(right, fieldPath, signalName);
    if (setAssignment) {
      assignments.push(setAssignment);
    }
    return true;
  }

  /** Pattern 7: someState.value = new Map([...someState.value, [key, val]]) (Map operations) */
  private tryExtractMapConstructorPattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value") || !isNewExpression(right)) return false;
    const constructorExpr = right.expression;
    if (!isIdentifier(constructorExpr) || textOf(constructorExpr) !== "Map") return false;

    const signalName = fieldPath.slice(0, -6);
    const mapAssignment = this.extractMapOperation(right, fieldPath, signalName);
    if (mapAssignment) {
      assignments.push(mapAssignment);
    }
    return true;
  }

  /**
   * Pattern 8: someState.value = expression (direct signal value assignment)
   * Matches signal.value = literal or signal.value = payload.xxx
   */
  private tryExtractSignalDirectValuePattern(
    fieldPath: string,
    right: Node,
    assignments: StateAssignment[]
  ): boolean {
    if (!fieldPath.endsWith(".value")) return false;
    const signalName = fieldPath.slice(0, -6);

    // Try extracting a primitive literal
    const literalValue = this.extractValue(right);
    if (literalValue !== undefined) {
      assignments.push({ field: signalName, value: literalValue });
      return true;
    }

    // Try extracting payload.xxx property access
    if (isPropertyAccessExpression(right)) {
      const rightPath = this.getPropertyPath(right);
      const parts = rightPath.split(".");
      if (
        parts.length === 2 &&
        parts[0] !== undefined &&
        parts[1] !== undefined &&
        this.currentFunctionParams.includes(parts[0])
      ) {
        assignments.push({ field: signalName, value: `param:${parts[1]}` });
        return true;
      }
    }

    return false;
  }

  /** Extract Set operations from new Set(...) constructor */
  private extractSetOperation(
    newExpr: NewExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const args = argumentsOf(newExpr);

    // new Set() - clear operation
    if (args.length === 0) {
      return { field: signalName, value: "{}" };
    }

    const firstArg = args[0];
    if (!firstArg) return null;

    // new Set([...set.value, item]) - add operation
    if (isArrayLiteralExpression(firstArg)) {
      return this.extractSetArrayOperation(firstArg, fieldPath, signalName);
    }

    // new Set([...set.value].filter(...)) - delete operation via method chain
    if (isCallExpression(firstArg)) {
      return this.extractSetMethodChainOperation(firstArg, fieldPath, signalName);
    }

    return null;
  }

  /** Extract Set operation from array literal: new Set([...set.value, item]) */
  private extractSetArrayOperation(
    arrayLiteral: ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.elements;
    if (elements.length < 1) return null;

    const firstElement = elements[0];
    const lastElement = elements[elements.length - 1];

    // Check for add: new Set([...set.value, item])
    if (firstElement && isSpreadElement(firstElement)) {
      const spreadExpr = firstElement.expression;
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        // Add operation: @ \union {payload}
        return { field: signalName, value: "@ \\union {payload}" };
      }
    }

    // Check for add at beginning: new Set([item, ...set.value])
    if (lastElement && isSpreadElement(lastElement)) {
      const spreadExpr = lastElement.expression;
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        return { field: signalName, value: "{payload} \\union @" };
      }
    }

    return null;
  }

  /** Extract Set operation from method chain: new Set([...set.value].filter(...)) */
  private extractSetMethodChainOperation(
    callExpr: CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.expression;
    if (!isPropertyAccessExpression(expression)) return null;

    const methodName = nameText(expression);
    const sourceExpr = expression.expression;

    // Check for [...set.value].filter(...) pattern
    if (methodName === "filter" && isArrayLiteralExpression(sourceExpr)) {
      const elements = sourceExpr.elements;
      if (elements.length === 1) {
        const spreadEl = elements[0];
        if (spreadEl && isSpreadElement(spreadEl)) {
          const spreadExpr = spreadEl.expression;
          if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
            // Delete operation: @ \ {payload}
            return { field: signalName, value: "@ \\ {payload}" };
          }
        }
      }
    }

    return null;
  }

  /** Extract Map operations from new Map(...) constructor */
  private extractMapOperation(
    newExpr: NewExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const args = argumentsOf(newExpr);

    // new Map() - clear operation
    if (args.length === 0) {
      return { field: signalName, value: "<<>>" }; // Empty function in TLA+
    }

    const firstArg = args[0];
    if (!firstArg) return null;

    // new Map([...map.value, [key, value]]) - set operation
    if (isArrayLiteralExpression(firstArg)) {
      return this.extractMapArrayOperation(firstArg, fieldPath, signalName);
    }

    // new Map([...map.value].filter(...)) - delete operation via method chain
    if (isCallExpression(firstArg)) {
      return this.extractMapMethodChainOperation(firstArg, fieldPath, signalName);
    }

    return null;
  }

  /** Extract Map operation from array literal: new Map([...map.value, [key, val]]) */
  private extractMapArrayOperation(
    arrayLiteral: ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.elements;
    if (elements.length < 1) return null;

    const firstElement = elements[0];

    // Check for set: new Map([...map.value, [key, value]])
    if (firstElement && isSpreadElement(firstElement)) {
      const spreadExpr = firstElement.expression;
      if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
        // Set operation: [@ EXCEPT ![payload.key] = payload.value]
        return { field: signalName, value: "[@ EXCEPT ![payload.key] = payload.value]" };
      }
    }

    return null;
  }

  /** Extract Map operation from method chain: new Map([...map.value].filter(...)) */
  private extractMapMethodChainOperation(
    callExpr: CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.expression;
    if (!isPropertyAccessExpression(expression)) return null;

    const methodName = nameText(expression);
    const sourceExpr = expression.expression;

    // Check for [...map.value].filter(...) pattern
    if (methodName === "filter" && isArrayLiteralExpression(sourceExpr)) {
      const elements = sourceExpr.elements;
      if (elements.length === 1) {
        const spreadEl = elements[0];
        if (spreadEl && isSpreadElement(spreadEl)) {
          const spreadExpr = spreadEl.expression;
          if (spreadExpr && this.getPropertyPath(spreadExpr) === fieldPath) {
            // Delete operation: restrict domain
            return { field: signalName, value: "[k \\in DOMAIN @ \\ {payload.key} |-> @[k]]" };
          }
        }
      }
    }

    return null;
  }

  /**
   * Extract array method operations: arr.filter(...), arr.map(...)
   */
  private extractArrayMethodOperation(
    callExpr: CallExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const expression = callExpr.expression;
    if (!isPropertyAccessExpression(expression)) return null;

    const methodName = nameText(expression);
    const sourceExpr = expression.expression;
    const sourcePath = this.getPropertyPath(sourceExpr);

    // Check if source matches target (e.g., todos.value = todos.value.filter(...))
    if (sourcePath !== fieldPath) return null;

    switch (methodName) {
      case "filter":
        // Non-deterministic element removal — codegen emits \E newLen
        return { field: signalName, value: "NDET:FILTER" };

      case "map":
        // Non-deterministic single-element modification — codegen emits \E mapIdx, mapVal
        return { field: signalName, value: "NDET:MAP" };

      case "slice":
        // Subsequence is semantically equivalent to filter in the abstract model
        return { field: signalName, value: "NDET:FILTER" };

      case "concat":
        // Concat appends another sequence
        return { field: signalName, value: "@ \\o <<payload>>" };

      case "reverse":
        // Reverse the sequence
        return { field: signalName, value: "[i \\in DOMAIN @ |-> @[Len(@) - i + 1]]" };

      default:
        // Warn about unsupported array methods
        this.warnUnsupportedArrayMethod(methodName, callExpr);
        return null;
    }
  }

  /** Warn about unsupported array methods */
  private warnUnsupportedArrayMethod(methodName: string, node: Node): void {
    const mutatingMethods = [
      "push",
      "pop",
      "shift",
      "unshift",
      "splice",
      "sort",
      "fill",
      "copyWithin",
    ];
    const queryMethods = [
      "find",
      "findIndex",
      "reduce",
      "reduceRight",
      "some",
      "every",
      "includes",
      "indexOf",
      "lastIndexOf",
    ];
    const otherMethods = ["flat", "flatMap", "join", "toString", "toLocaleString"];

    if (mutatingMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' mutates in place. Use spread syntax: [...arr, item] for append, arr.filter() for removal.`
      );
    } else if (queryMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' returns a single value, not a new array. State assignment won't be extracted.`
      );
    } else if (otherMethods.includes(methodName)) {
      this.warnUnsupportedPattern(
        `array.${methodName}()`,
        this.getNodeLocation(node),
        `'${methodName}' is not supported for state extraction. Consider using map/filter instead.`
      );
    }
  }

  /**
   * Extract assignments from spread update pattern: { ...existing, field: value }
   * Only extracts the explicitly set properties, not the spread
   */
  private extractSpreadUpdateAssignments(
    objectLiteral: ObjectLiteralExpression,
    assignments: StateAssignment[],
    signalName: string
  ): void {
    for (const prop of objectLiteral.properties) {
      // Skip spread assignments (they preserve existing values)
      if (isSpreadAssignment(prop)) continue;

      // Extract regular property assignments
      this.extractPropertyAssignment(prop, assignments, signalName);
    }
  }

  /**
   * Extract array spread operations: [...arr, item] or [item, ...arr]
   */
  private extractArraySpreadOperation(
    arrayLiteral: ArrayLiteralExpression,
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const elements = arrayLiteral.elements;
    if (elements.length < 1) return null;

    // Try append pattern first, then prepend
    return (
      this.tryExtractAppendOperation(elements, fieldPath, signalName) ??
      this.tryExtractPrependOperation(elements, fieldPath, signalName)
    );
  }

  /** Extract append operation: [...arr, item] or [...arr, item1, item2] */
  private tryExtractAppendOperation(
    elements: readonly Node[],
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    const firstElement = elements[0];
    if (!firstElement || !isSpreadElement(firstElement)) return null;

    const spreadExpr = firstElement.expression;
    if (!spreadExpr || this.getPropertyPath(spreadExpr) !== fieldPath) return null;

    if (elements.length === 2) {
      return { field: signalName, value: "Append(@, payload)" };
    }
    const placeholders = Array(elements.length - 1)
      .fill("payload")
      .join(", ");
    return { field: signalName, value: `@ \\o <<${placeholders}>>` };
  }

  /** Extract prepend operation: [item, ...arr] or [item1, item2, ...arr] */
  private tryExtractPrependOperation(
    elements: readonly Node[],
    fieldPath: string,
    signalName: string
  ): StateAssignment | null {
    if (elements.length < 2) return null;

    const lastElement = elements[elements.length - 1];
    if (!lastElement || !isSpreadElement(lastElement)) return null;

    const spreadExpr = lastElement.expression;
    if (!spreadExpr || this.getPropertyPath(spreadExpr) !== fieldPath) return null;

    if (elements.length === 2) {
      return { field: signalName, value: "<<payload>> \\o @" };
    }
    const placeholders = Array(elements.length - 1)
      .fill("payload")
      .join(", ");
    return { field: signalName, value: `<<${placeholders}>> \\o @` };
  }

  /**
   * Extract assignments from object literal properties
   * Used for: someState.value = { field1: value1, field2: value2 }
   * @param signalName - Optional signal name prefix (e.g., "user" for user.value = {...})
   */
  private extractObjectLiteralAssignments(
    objectLiteral: Node,
    assignments: StateAssignment[],
    signalName?: string
  ): void {
    if (!isObjectLiteralExpression(objectLiteral)) return;

    for (const prop of objectLiteral.properties) {
      this.extractPropertyAssignment(prop, assignments, signalName);
    }
  }

  /**
   * Extract a single property assignment from an object literal property
   */
  private extractPropertyAssignment(
    prop: Node,
    assignments: StateAssignment[],
    signalName?: string
  ): void {
    // Handle regular property assignments: { field: value }
    if (isPropertyAssignment(prop)) {
      this.extractRegularPropertyAssignment(prop, assignments, signalName);
      return;
    }

    // Handle shorthand properties: { field }
    if (isShorthandPropertyAssignment(prop)) {
      const name = nameText(prop);
      const field = signalName ? `${signalName}_${name}` : name;
      // If the identifier matches a function parameter, trace it to payload
      if (this.currentFunctionParams.includes(name)) {
        assignments.push({ field, value: `param:${name}` });
      } else {
        // For shorthand, we can't extract the value statically
        // but we know the field is being set
        assignments.push({ field, value: "@" }); // Use @ as placeholder
      }
    }
  }

  /**
   * Handle the regular `{ field: value }` form within an object literal.
   * Splits the literal-extraction and payload-property-tracing paths so the
   * outer dispatcher stays simple and biome's cognitive-complexity budget
   * holds.
   */
  private extractRegularPropertyAssignment(
    prop: Node,
    assignments: StateAssignment[],
    signalName?: string
  ): void {
    if (!isPropertyAssignment(prop)) return;
    const name = nameText(prop);
    const initializer = prop.initializer;
    if (!name || !initializer) return;

    const field = signalName ? `${signalName}_${name}` : name;

    const value = this.extractValue(initializer);
    if (value !== undefined) {
      assignments.push({ field, value });
      return;
    }

    // Trace `field: paramName` (renamed-property form, e.g.
    // `currentView: view`) to the payload identifier. The shorthand
    // `{ view }` form already does this; without this branch the renamed
    // form silently drops the assignment from the action body and leaves
    // ensures references to the parameter unbound (issue #77).
    if (isIdentifier(initializer)) {
      const paramName = textOf(initializer);
      if (this.currentFunctionParams.includes(paramName)) {
        assignments.push({ field, value: `param:${paramName}` });
        return;
      }
    }

    // Trace `field: paramName.X` (e.g. `role: payload.role`) to the payload
    // field. Mirrors the shorthand `{ field }` and direct `signal.value =
    // paramName.X` paths so longhand object literals participate in
    // payload-domain wiring (issue #72) and per-action ensures Asserts
    // (issue #73) the same way the other forms do.
    const paramName = this.extractPayloadPropertyParam(initializer);
    if (paramName !== null) {
      assignments.push({ field, value: `param:${paramName}` });
      return;
    }

    // polly#147: a non-literal initializer that is a translatable expression —
    // arithmetic on the signal's own field (`outstanding + 1`), a copy of
    // another field, an index access — is captured verbatim and translated to
    // TLA+ at codegen time, mirroring how `state.foo += 1` keeps its RHS via
    // `textOf(right)`. Without this the assignment was silently dropped, so a
    // counter `signal.value = { outstanding: signal.value.outstanding + 1 }`
    // generated an UNCHANGED stub and its bounded-counter ensures could never
    // be anchored.
    if (this.isTranslatableInitializer(initializer)) {
      // polly#169: resolve `const x = sig.value` aliases before the text leaves
      // the function that gave its identifiers meaning.
      // polly#170: strip redundant outer parentheses — `translateTernary` is a
      // regex and chops across them, producing `IF (a THEN 1 ELSE 0)`.
      const captured = this.resolveSignalAliases(this.unwrapParentheses(initializer));
      assignments.push({ field, value: `EXPR:${captured}` });
      return;
    }

    // polly#144 set the precedent that a silently dropped handler is the core
    // failure mode, so its warning is unconditional. The same applies here: a
    // dropped property models the field as never moving, and every property
    // written over it then holds vacuously (polly#170).
    const on = signalName ? ` on ${signalName}.value` : "";
    console.log(
      `[WARN] dropped object-literal property '${name}'${on} — initializer \`${textOf(initializer).replace(/\s+/g, " ").slice(0, 80)}\` (${kindName(initializer)}) is not translatable to TLA+`
    );
  }

  /**
   * polly#169: rewrite `<alias>.field` back to `<signal>.value.field`.
   *
   * The `EXPR:` capture hands source text to a codegen translator that resolves
   * signal references by shape, not by binding. A handler that reads through
   * `const state = offlineQueue.value` emitted `state.unsyncedChanges`, which
   * the translator's `state.` rule rewrote to `contextStates[ctx].unsyncedChanges`
   * — a member that does not exist, because the record carries
   * `offlineQueue_unsyncedChanges`. An alias under any other name reached SANY
   * as a free identifier.
   *
   * Aliases are collected from the initializer's OWN enclosing function rather
   * than from extractor instance state: an object literal is reached by two
   * walks (`extractAssignments`, and `findStateMutationsInFunction` for the
   * issue-#27 lift pass) and only one passes through the handler entry points
   * that maintain instance state, so state held on `this` would silently do
   * nothing on the other.
   *
   * Rewriting is driven by AST node positions, not by a regex over the text —
   * a regex is what made the original defect possible.
   */
  private resolveSignalAliases(initializer: Node): string {
    const aliases = this.collectSignalAliases(initializer);
    if (aliases.size === 0) return textOf(initializer);

    const base = startOf(initializer);
    const edits: Array<{ start: number; end: number; text: string }> = [];

    // forEachDescendant excludes the node itself, and the initializer is often
    // the whole access (`o.count`), so visit the root as well.
    const visit = (node: Node): void => {
      if (!isPropertyAccessExpression(node)) return;
      const target = node.expression;
      if (!isIdentifier(target)) return;
      const signal = aliases.get(textOf(target));
      if (!signal) return;
      edits.push({
        start: startOf(target) - base,
        end: target.end - base,
        text: `${signal}.value`,
      });
    };
    visit(initializer);
    forEachDescendant(initializer, visit);

    if (edits.length === 0) return textOf(initializer);

    let text = textOf(initializer);
    for (const edit of edits.sort((a, b) => b.start - a.start)) {
      text = text.slice(0, edit.start) + edit.text + text.slice(edit.end);
    }
    return text;
  }

  /**
   * Collect `const <name> = <ident>.value` bindings from the nearest enclosing
   * function of `node`.
   *
   * Deliberately narrow. Destructuring, a reassigned `let`, and an alias of an
   * alias are left untranslated and fall through to the warning: a wrong entry
   * rewrites an expression into a field that DOES exist, which is strictly
   * worse than one that fails loudly.
   */
  private collectSignalAliases(node: Node): Map<string, string> {
    const aliases = new Map<string, string>();

    const fn = firstAncestor(
      node,
      (a): a is ArrowFunction | FunctionExpression | FunctionDeclaration =>
        isArrowFunction(a) || isFunctionExpression(a) || isFunctionDeclaration(a)
    );
    if (!fn) return aliases;

    const reassigned = this.collectReassignedIdentifiers(fn);

    forEachDescendant(fn, (inner) => {
      if (!isVariableDeclaration(inner)) return;
      const binding = this.readSignalAliasBinding(inner);
      if (!binding) return;
      // An alias of an alias, and a rebound name, are both left untranslated.
      if (aliases.has(binding.signal)) return;
      if (reassigned.has(binding.alias)) return;
      aliases.set(binding.alias, binding.signal);
    });

    return aliases;
  }

  /** Identifiers assigned anywhere in `fn`, so a rebound alias can be ignored. */
  private collectReassignedIdentifiers(fn: Node): Set<string> {
    const reassigned = new Set<string>();
    forEachDescendant(fn, (inner) => {
      if (!isBinaryExpression(inner)) return;
      if (textOf(inner.operatorToken) !== "=") return;
      const left = inner.left;
      if (isIdentifier(left)) reassigned.add(textOf(left));
    });
    return reassigned;
  }

  /**
   * Read `const <alias> = <signal>.value` from a declaration, or null.
   *
   * `const` only (a `let` may be rebound between the alias and its use), a plain
   * identifier only (a destructuring pattern binds fields, not the object), and
   * `<identifier>.value` only (not `a.b.value`).
   */
  private readSignalAliasBinding(
    decl: VariableDeclaration
  ): { alias: string; signal: string } | null {
    const list = decl.parent;
    if (!isVariableDeclarationList(list)) return null;
    if (declarationKind(list) !== "const") return null;

    const nameNode = decl.name;
    if (!isIdentifier(nameNode)) return null;

    const init = decl.initializer;
    if (!init || !isPropertyAccessExpression(init)) return null;
    if (nameText(init) !== "value") return null;

    const target = init.expression;
    if (!isIdentifier(target)) return null;

    return { alias: textOf(nameNode), signal: textOf(target) };
  }

  /**
   * Whether an object-literal property initializer is an expression the codegen
   * translator (`tsExpressionToTLA`) handles reliably (polly#147). Literals and
   * payload-parameter references are resolved before this is reached; this
   * covers arithmetic, member/index access, (un)parenthesized unary forms and —
   * since polly#170 — a single ternary.
   *
   * polly#170: the original "conditional expressions are excluded" rule was
   * both too strict and too loose. Too strict, because `translateTernary`
   * (tools/verify codegen) does translate a single comment-free ternary
   * correctly, and dropping it modelled the field as never moving. Too loose,
   * because the kind checks below admit a ternary nested inside a binary or a
   * parenthesized expression, and a call nested anywhere — `translateTernary`
   * is a regex, so `{ x: (a ? 1 : 0) }` became `IF (a THEN 1 ELSE 0)` with
   * unbalanced parentheses.
   *
   * The subtree checks close both halves: reject a call or a nested ternary
   * wherever it appears, and reject a comment, whose `//` is carried into the
   * generated line and can corrupt the quote-conversion pass.
   */
  private isTranslatableInitializer(node: Node): boolean {
    const kindAllowed =
      isBinaryExpression(node) ||
      isPropertyAccessExpression(node) ||
      isElementAccessExpression(node) ||
      isPrefixUnaryExpression(node) ||
      isPostfixUnaryExpression(node) ||
      isParenthesizedExpression(node) ||
      isConditionalExpression(node);

    if (!kindAllowed) return false;
    if (this.containsComment(node)) return false;
    if (firstDescendant(node, isCallExpression)) return false;

    // A ternary is admitted only as the whole expression, and only one deep.
    // Unwrap parentheses first: a nested ternary is normally written
    // `a ? (b ? c : d) : e`, so a check that inspects the branch nodes directly
    // reads that as a single ternary and admits it. `getFirstDescendantByKind`
    // excludes the node itself, so this rejects a ternary nested under a root
    // ternary and a ternary anywhere under a binary or parenthesized root — the
    // two shapes `translateTernary`'s regex gets wrong — while admitting a root
    // ternary with none below it.
    return firstDescendant(this.unwrapParentheses(node), isConditionalExpression) === undefined;
  }

  /** Strip redundant parentheses, so branch checks see the real node. */
  private unwrapParentheses(node: Node): Node {
    let current = node;
    while (isParenthesizedExpression(current)) {
      current = current.expression;
    }
    return current;
  }

  /**
   * Whether a node's source text carries a comment. A `//` inside a captured
   * expression is carried verbatim into the generated TLA+ line (polly#170).
   */
  private containsComment(node: Node): boolean {
    const text = textOf(node);
    return text.includes("//") || text.includes("/*");
  }

  /**
   * If `initializer` is `paramName.X` where paramName is a function parameter
   * of the current handler, return X. Otherwise return null.
   */
  private extractPayloadPropertyParam(initializer: Node): string | null {
    if (!isPropertyAccessExpression(initializer)) return null;
    const parts = this.getPropertyPath(initializer).split(".");
    if (parts.length !== 2) return null;
    const [paramName, fieldName] = parts;
    if (paramName === undefined || fieldName === undefined) return null;
    if (!this.currentFunctionParams.includes(paramName)) return null;
    return fieldName;
  }

  /**
   * Extract element access assignment (state.items[index] = value)
   */
  private extractElementAccessAssignment(
    left: Node,
    right: Node,
    assignments: StateAssignment[]
  ): void {
    if (!isElementAccessExpression(left)) return;

    const expr = left.expression;
    if (!isPropertyAccessExpression(expr)) return;

    const fieldPath = this.getPropertyPath(expr);
    const field = this.extractFieldFromStatePath(fieldPath);

    if (!field) return;
    const indexExpr = left.argumentExpression;
    const index = indexExpr ? textOf(indexExpr) : "0";
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
   * Check if field path is a state mutation pattern and extract field name
   * Supports: state.field, someState.value.field
   * Returns: field name or null if not a state pattern
   */
  private extractFieldFromStatePath(fieldPath: string): string | null {
    // Pattern 1: state.field
    if (fieldPath.startsWith("state.")) {
      return fieldPath.substring(6);
    }

    // Pattern 2: someState.value.field
    const valueMatch = fieldPath.match(/\.value\.(.+)$/);
    if (valueMatch?.[1]) {
      return valueMatch[1];
    }

    return null;
  }

  /**
   * The field a numeric update (`++`, `--`, `+=`, ...) writes. Besides the
   * object paths, a primitive signal's own `.value` names the signal, as a
   * literal write to it does (Pattern 8): `count.value++` writes `count`.
   * Without this, the update was dropped and the action emitted UNCHANGED.
   */
  private extractNumericUpdateField(fieldPath: string): string | null {
    const field = this.extractFieldFromStatePath(fieldPath);
    if (field) return field;
    if (fieldPath.endsWith(".value") && !fieldPath.slice(0, -6).includes(".")) {
      return fieldPath.slice(0, -6);
    }
    return null;
  }

  /**
   * Extract compound assignments (+=, -=, *=, /=, %=)
   */
  private extractCompoundAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!isBinaryExpression(node)) return;

    const operator = textOf(node.operatorToken);
    const left = node.left;
    const right = node.right;

    if (isPropertyAccessExpression(left)) {
      const fieldPath = this.getPropertyPath(left);
      const field = this.extractNumericUpdateField(fieldPath);

      if (field) {
        const rightValue = textOf(right);
        const tlaOp = operator.slice(0, -1); // Remove '=' suffix
        assignments.push({
          field,
          value: `@ ${tlaOp} ${rightValue}`,
        });
      }
    }
  }

  /**
   * Get operator text from a unary expression's operator (a SyntaxKind; ts-morph's
   * `getOperatorToken()` returned the same number for both unary kinds)
   */
  private getUnaryOperatorText(operator: SyntaxKind): string | null {
    if (operator === SyntaxKind.PlusPlusToken) return "++";
    if (operator === SyntaxKind.MinusMinusToken) return "--";
    return null;
  }

  /**
   * Extract unary expression assignments (++, --)
   */
  private extractUnaryExpressionAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!isPostfixUnaryExpression(node) && !isPrefixUnaryExpression(node)) return;

    const operator = node.operator;
    const operatorText = this.getUnaryOperatorText(operator);

    // Only handle ++ and --
    if (operatorText !== "++" && operatorText !== "--") return;

    const operand = node.operand;
    if (!isPropertyAccessExpression(operand)) return;

    const fieldPath = this.getPropertyPath(operand);
    const field = this.extractNumericUpdateField(fieldPath);

    if (field) {
      // Translate ++ to @ + 1 and -- to @ - 1
      const value = operatorText === "++" ? "@ + 1" : "@ - 1";
      assignments.push({ field, value });
    }
  }

  /**
   * Extract array mutation assignments (push, pop, shift, unshift, splice)
   */
  private extractArrayMutationAssignment(node: Node, assignments: StateAssignment[]): void {
    if (!isCallExpression(node)) return;

    const expr = node.expression;
    if (!isPropertyAccessExpression(expr)) return;

    const methodName = nameText(expr);
    const object = expr.expression;

    if (isPropertyAccessExpression(object)) {
      const fieldPath = this.getPropertyPath(object);
      const field = this.extractFieldFromStatePath(fieldPath);

      if (field) {
        const args = node.arguments.map((arg) => textOf(arg));
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
    const isAsync = funcNode.modifiers?.some((m) => m.kind === SyntaxKind.AsyncKeyword) ?? false;

    if (!isAsync) {
      return; // Not async, no race conditions possible
    }

    // Find all await expressions
    const awaitExpressions: Node[] = [];
    forEachDescendant(funcNode, (node: Node) => {
      if (isAwaitExpression(node)) {
        awaitExpressions.push(node);
      }
    });

    if (awaitExpressions.length === 0) {
      return; // No awaits, no interleaving possible
    }

    // Find all state mutations
    const mutations: Array<{ field: string; line: number; afterAwait: boolean }> = [];
    const body = funcNode.body;

    if (!body) {
      return;
    }

    const firstAwait = awaitExpressions[0];
    if (!firstAwait) return;

    // Get position of first await
    const firstAwaitPos = startOf(firstAwait);

    // Track mutations and whether they occur after await
    forEachDescendant(funcNode, (node: Node) => {
      if (isBinaryExpression(node)) {
        this.checkBinaryExpressionMutation(node, firstAwaitPos, mutations);
      }

      if (isCallExpression(node)) {
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
    funcNode: HandlerFunction,
    preconditions: VerificationCondition[],
    postconditions: VerificationCondition[]
  ): void {
    const body = funcNode.body;
    const statements = body && isBlock(body) ? body.statements : body ? [body] : [];

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
    if (!isExpressionStatement(statement)) return;

    const expr = statement.expression;
    if (!isCallExpression(expr)) return;

    const callee = expr.expression;
    if (!isIdentifier(callee)) return;

    const functionName = textOf(callee);

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
    const args = callExpr.arguments;

    if (args.length === 0) {
      return null;
    }

    // First argument is the condition expression
    const conditionArg = args[0];
    if (!conditionArg) return null;

    const expression = textOf(conditionArg);

    // Second argument (optional) is the message
    let message: string | undefined;
    const messageArg = args[1];
    if (args.length >= 2 && messageArg && isStringLiteral(messageArg)) {
      message = messageArg.text;
    }

    const line = startLine(callExpr);
    const column = startLinePos(callExpr);

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
    while (isPropertyAccessExpression(current)) {
      parts.unshift(nameText(current));
      current = current.expression;
    }

    // Add the base identifier
    if (isIdentifier(current)) {
      parts.unshift(textOf(current));
    }

    return parts.join(".");
  }

  /**
   * Extract a literal value from an expression
   */
  private extractValue(node: Node): string | boolean | number | null | undefined {
    if (isStringLiteral(node)) {
      return node.text;
    }

    if (isNumericLiteral(node)) {
      return literalValue(node);
    }

    if (node.kind === SyntaxKind.TrueKeyword) {
      return true;
    }

    if (node.kind === SyntaxKind.FalseKeyword) {
      return false;
    }

    if (node.kind === SyntaxKind.NullKeyword) {
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
      const expression = switchNode.expression;
      const expressionText = textOf(expression);

      // Look for patterns like: message.type, data.type, msg.type, event.type
      if (!/\.(type|kind|event|action)/.test(expressionText)) {
        return handlers;
      }

      // Extract handlers from each case clause
      const caseClauses = switchNode.caseBlock.clauses;
      for (const clause of caseClauses) {
        if (isCaseClause(clause)) {
          const caseExpr = clause.expression;

          // Extract message type from case expression
          let messageType: string | null = null;
          if (isStringLiteral(caseExpr)) {
            messageType = caseExpr.text;
          }

          if (messageType) {
            const line = startLine(clause);

            handlers.push({
              messageType,
              node: context,
              assignments: [],
              preconditions: [],
              postconditions: [],
              location: { file: filePath, line },
              origin: "event" as const,
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
      const initializer = varDecl.initializer;
      if (!initializer) {
        return handlers;
      }

      // Get the object literal - either direct or from defineHandlers() call
      const objectLiteral = this.getHandlerMapObject(initializer, varDecl);
      if (!objectLiteral) {
        return handlers;
      }

      // Extract handlers from object properties
      const properties = objectLiteral.properties;
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
   * Extract the object literal from a handler map.
   * Only processes direct object literals with handler-like variable names.
   */
  private getHandlerMapObject(
    initializer: Node,
    varDecl: VariableDeclaration
  ): ObjectLiteralExpression | null {
    // Only process direct object literals
    if (isObjectLiteralExpression(initializer)) {
      if (this.isHandlerMapName(nameText(varDecl))) {
        return initializer;
      }
    }
    return null;
  }

  /**
   * Check if variable name suggests it's a handler map
   */
  private isHandlerMapName(varName: string): boolean {
    return /(handler|listener|callback|event)s?/.test(varName.toLowerCase());
  }

  /**
   * Extract handler from a property assignment in a handler map
   */
  private extractHandlerFromProperty(
    prop: Node,
    context: string,
    filePath: string
  ): MessageHandler | null {
    if (!isPropertyAssignment(prop)) {
      return null;
    }

    const nameNode = prop.name;
    const messageType = this.getMessageTypeFromPropertyName(nameNode);

    if (!messageType) {
      return null;
    }

    const value = prop.initializer;
    const assignments: StateAssignment[] = [];
    const preconditions: VerificationCondition[] = [];
    const postconditions: VerificationCondition[] = [];

    // Extract from the handler function
    if (value) {
      // Case 1: Inline arrow function or function expression
      if (isArrowFunction(value) || isFunctionExpression(value)) {
        this.extractAssignments(value, assignments);
        this.extractVerificationConditions(value, preconditions, postconditions);
      }
      // Case 2: Function reference (e.g., handleQuery)
      else if (isIdentifier(value)) {
        const referencedFunction = this.resolveFunctionReference(value);
        if (referencedFunction) {
          this.extractAssignments(referencedFunction, assignments);
          this.extractVerificationConditions(referencedFunction, preconditions, postconditions);
        }
      }
    }

    const line = startLine(prop);
    return {
      messageType,
      node: context,
      assignments,
      preconditions,
      postconditions,
      location: { file: filePath, line },
    };
  }

  /**
   * Extract message type from property name node
   */
  private getMessageTypeFromPropertyName(nameNode: Node): string | null {
    if (isStringLiteral(nameNode)) {
      return nameNode.text;
    }
    if (isIdentifier(nameNode)) {
      return textOf(nameNode);
    }
    return null;
  }

  /**
   * Resolve a function reference to its declaration or expression.
   * Handles both named function declarations and variable-assigned functions.
   *
   * @param identifier - The identifier node referencing the function
   * @returns The resolved function node, or null if not found
   */
  private resolveFunctionReference(
    identifier: Node
  ): FunctionDeclaration | ArrowFunction | FunctionExpression | null {
    if (!isIdentifier(identifier)) {
      return null;
    }

    try {
      const definitions = this.definitionsOf(identifier);

      for (const def of definitions) {
        // Direct function declaration
        if (isFunctionDeclaration(def)) {
          return def;
        }

        // Variable declaration with function initializer
        if (isVariableDeclaration(def)) {
          const initializer = def.initializer;
          if (initializer && (isArrowFunction(initializer) || isFunctionExpression(initializer))) {
            return initializer;
          }
        }
      }
    } catch (_error) {
      // Failed to resolve - return null
    }

    return null;
  }

  /**
   * Extract handlers from type guard if/else-if patterns
   * Detects: if (isQueryMessage(msg)) { handleQuery(msg); }
   */
  private extractTypeGuardHandlers(
    ifNode: IfStatement,
    context: string,
    filePath: string
  ): MessageHandler[] {
    const handlers: MessageHandler[] = [];

    try {
      const sourceFile = ifNode.getSourceFile();
      const typeGuards = this.getOrComputeTypeGuards(sourceFile);

      this.debugLogTypeGuards(sourceFile, typeGuards);
      this.processIfElseChain(ifNode, typeGuards, context, filePath, handlers);
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

    console.log(`[DEBUG] File: ${basename(sourceFile.fileName)}`);
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
      const elseStatement = ifStatement.elseStatement;
      if (elseStatement && isIfStatement(elseStatement)) {
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
    ifStmt: IfStatement,
    typeGuards: Map<string, string>,
    context: string,
    filePath: string
  ): MessageHandler | null {
    try {
      const condition = ifStmt.expression;

      // Pattern 1: Type guard function call — if (isSubscribe(msg))
      if (isCallExpression(condition)) {
        const funcExpr = condition.expression;
        const funcName = isIdentifier(funcExpr) ? textOf(funcExpr) : undefined;

        this.debugLogProcessingFunction(funcName);

        const messageType = this.resolveMessageType(funcExpr, funcName, typeGuards);
        if (!messageType) {
          this.debugLogUnresolvedMessageType(funcName);
          return null;
        }

        const line = startLine(ifStmt);
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
      }

      // Pattern 2: Equality check — if (data.type === 'subscribe')
      if (isBinaryExpression(condition)) {
        const messageType = this.extractMessageTypeFromEqualityCheck(condition);
        if (messageType) {
          const line = startLine(ifStmt);
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
        }
      }

      return null;
    } catch (_error) {
      return null;
    }
  }

  /**
   * Extract message type from equality check: data.type === 'subscribe'
   */
  private extractMessageTypeFromEqualityCheck(expr: BinaryExpression): string | null {
    const operator = textOf(expr.operatorToken);
    if (operator !== "===" && operator !== "==") return null;

    const left = expr.left;
    const right = expr.right;

    // Check: xxx.type === 'value' or 'value' === xxx.type
    const stringLiteral = isStringLiteral(right) ? right : isStringLiteral(left) ? left : null;
    const propAccess = isPropertyAccessExpression(left)
      ? left
      : isPropertyAccessExpression(right)
        ? right
        : null;

    if (!stringLiteral || !propAccess) return null;

    const propName = nameText(propAccess);
    if (propName !== "type" && propName !== "kind" && propName !== "action") {
      return null;
    }

    return stringLiteral.text;
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

    if (isIdentifier(funcExpr)) {
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
    const thenStatement = ifStmt.thenStatement;
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

    forEachDescendant(sourceFile, (node) => {
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

    const returnTypeNode = node.type;
    if (!returnTypeNode || !isTypePredicateNode(returnTypeNode)) {
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
    if (isFunctionDeclaration(node)) {
      return nameOf(node);
    }

    if (isFunctionExpression(node) || isArrowFunction(node)) {
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
    const parent = node.parent;
    if (isVariableDeclaration(parent)) {
      return nameText(parent);
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
    if (!isTypePredicateNode(returnTypeNode)) {
      return null;
    }

    // The predicate's type node (absent for `asserts x`)
    const typeNode = returnTypeNode.type;
    if (typeNode) {
      const typeName = textOf(typeNode);
      const messageType = this.extractMessageTypeFromTypeName(typeName);
      if (messageType) {
        return messageType;
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
    const body = node.body;
    if (!body) {
      return null;
    }

    const bodyText = textOf(body);
    const typeValueMatch = bodyText.match(/\.type\s*===?\s*['"](\w+)['"]/);

    if (typeValueMatch) {
      return typeValueMatch[1] ?? null;
    }

    return null;
  }

  /**
   * Resolve type guard from imported function
   * Uses go-to-definition (prefetched) to find the definition across files
   * Checks AST structure, not resolved types (which can lose type predicate info)
   */
  private resolveImportedTypeGuard(identifier: Identifier): string | null {
    try {
      const funcName = textOf(identifier);
      const definitions = this.definitionsOf(identifier);

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

    const returnTypeNode = def.type;
    this.debugLogReturnTypeInfo(funcName, returnTypeNode);

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
    return isFunctionDeclaration(node) || isFunctionExpression(node) || isArrowFunction(node);
  }

  /**
   * Extract message type from type predicate node
   */
  private extractFromTypePredicate(
    returnTypeNode: Node | undefined,
    funcName: string
  ): string | null {
    if (!returnTypeNode || !isTypePredicateNode(returnTypeNode)) {
      return null;
    }

    const typeNode = returnTypeNode.type;
    if (!typeNode) {
      return null;
    }

    const typeName = textOf(typeNode);
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
    const body = def.body;
    if (!body) {
      return null;
    }

    const bodyText = textOf(body);
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
  private debugLogReturnTypeInfo(funcName: string, returnTypeNode: Node | undefined): void {
    if (process.env["POLLY_DEBUG"]) {
      // The resolved return type needs the checker; the declared one is logged instead.
      const returnType = returnTypeNode ? textOf(returnTypeNode) : "(not declared)";
      console.log(`[DEBUG] Function ${funcName} return type (declared): ${returnType}`);
      console.log(`[DEBUG] Has return type node: ${!!returnTypeNode}`);
      console.log(
        `[DEBUG] Is type predicate node: ${returnTypeNode && isTypePredicateNode(returnTypeNode)}`
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
    // An object type literal (`value is { success: true }`) narrows a shape,
    // not a message: it names no message type, so the guard is no handler
    // unless its body compares `.type`.
    if (typeName.trimStart().startsWith("{")) return "";

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
    // Check context overrides first (monorepo workspace packages)
    for (const [pathPrefix, context] of this.contextOverrides.entries()) {
      if (filePath.startsWith(pathPrefix)) return context;
    }

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
    if (!isBinaryExpression(node)) return;

    const operator = textOf(node.operatorToken);
    if (operator !== "=" && !["+=", "-=", "*=", "/=", "%="].includes(operator)) return;

    const left = node.left;
    if (!isPropertyAccessExpression(left) && !isElementAccessExpression(left)) return;

    const fieldPath = isPropertyAccessExpression(left)
      ? this.getPropertyPath(left)
      : this.getPropertyPath(left.expression);

    const field = this.extractFieldFromStatePath(fieldPath);
    if (field) {
      const line = startLine(node);
      const afterAwait = startOf(node) > firstAwaitPos;
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
    if (!isCallExpression(node)) return;

    const expr = node.expression;
    if (!isPropertyAccessExpression(expr)) return;

    const methodName = nameText(expr);
    const object = expr.expression;

    if (!isPropertyAccessExpression(object)) return;

    const fieldPath = this.getPropertyPath(object);
    const field = this.extractFieldFromStatePath(fieldPath);

    if (field && ["push", "pop", "shift", "unshift", "splice"].includes(methodName)) {
      const line = startLine(node);
      const afterAwait = startOf(node) > firstAwaitPos;
      mutations.push({ field, line, afterAwait });
    }
  }

  /**
   * Extract state-level constraints from a source file
   */
  private extractStateConstraintsFromFile(sourceFile: SourceFile): StateConstraint[] {
    const constraints: StateConstraint[] = [];
    const filePath = sourceFile.fileName;

    forEachDescendant(sourceFile, (node) => {
      const nodeConstraints = this.recognizeStateConstraint(node, filePath);
      constraints.push(...nodeConstraints);
    });

    return constraints;
  }

  /**
   * Extract global state constraints (stateConstraint() calls) from a source file
   */
  private extractGlobalStateConstraintsFromFile(sourceFile: SourceFile): GlobalStateConstraint[] {
    const constraints: GlobalStateConstraint[] = [];
    const filePath = sourceFile.fileName;

    forEachDescendant(sourceFile, (node) => {
      const constraint = this.recognizeGlobalStateConstraint(node, filePath);
      if (constraint) {
        constraints.push(constraint);
      }
    });

    return constraints;
  }

  /**
   * Recognize a stateConstraint() call and extract the constraint definition
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Parser logic requires nested conditionals
  private recognizeGlobalStateConstraint(
    node: Node,
    filePath: string
  ): GlobalStateConstraint | null {
    if (!isCallExpression(node)) {
      return null;
    }

    const expression = node.expression;
    if (!isIdentifier(expression)) {
      return null;
    }

    const functionName = textOf(expression);
    if (functionName !== "stateConstraint") {
      return null;
    }

    const args = node.arguments;
    if (args.length < 2) {
      return null;
    }

    // Arg 0: string literal → name
    const nameArg = args[0];
    if (!nameArg || !isStringLiteral(nameArg)) {
      return null;
    }
    const name = nameArg.text;

    // Arg 1: arrow function → extract body expression
    const predicateArg = args[1];
    if (!predicateArg || !isArrowFunction(predicateArg)) {
      return null;
    }

    const body = predicateArg.body;
    let expressionText: string;

    if (isBlock(body)) {
      // Block body: find return statement
      const returnStatement = body.statements.find((s) => isReturnStatement(s));
      if (!returnStatement || !isReturnStatement(returnStatement)) {
        return null;
      }
      const returnExpr = returnStatement.expression;
      if (!returnExpr) {
        return null;
      }
      expressionText = textOf(returnExpr);
    } else {
      // Expression body
      expressionText = textOf(body);
    }

    // Arg 2 (optional): object literal with message property
    let message: string | undefined;
    if (args.length >= 3) {
      const optionsArg = args[2];
      if (optionsArg && isObjectLiteralExpression(optionsArg)) {
        for (const prop of optionsArg.properties) {
          if (isPropertyAssignment(prop) && nameText(prop) === "message") {
            const value = prop.initializer;
            if (value && isStringLiteral(value)) {
              message = value.text;
            }
          }
        }
      }
    }

    return {
      name,
      expression: expressionText,
      message,
      location: {
        file: filePath,
        line: startLine(node),
      },
    };
  }

  /**
   * Recognize a $constraints() call and extract constraint definitions
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Parser logic requires nested conditionals
  private recognizeStateConstraint(node: Node, filePath: string): StateConstraint[] {
    if (!isCallExpression(node)) {
      return [];
    }

    const expression = node.expression;
    if (!isIdentifier(expression)) {
      return [];
    }

    const functionName = textOf(expression);
    if (functionName !== "$constraints") {
      return [];
    }

    // Get arguments: $constraints(field, constraintsObject)
    const args = node.arguments;
    if (args.length < 2) {
      return [];
    }

    // First argument is the state field name
    const fieldArg = args[0];
    if (!fieldArg || !isStringLiteral(fieldArg)) {
      return [];
    }
    const field = fieldArg.text;

    // Second argument is the constraints object
    const constraintsArg = args[1];
    if (!constraintsArg || !isObjectLiteralExpression(constraintsArg)) {
      return [];
    }

    // Extract each message type constraint
    const results: StateConstraint[] = [];
    for (const property of constraintsArg.properties) {
      if (!isPropertyAssignment(property)) {
        continue;
      }

      const messageType = nameText(property);
      const initializer = property.initializer;
      if (!initializer || !isObjectLiteralExpression(initializer)) {
        continue;
      }

      // Extract requires, ensures, and message from the constraint object
      let requires: string | undefined;
      let ensures: string | undefined;
      let message: string | undefined;

      for (const constraintProp of initializer.properties) {
        if (!isPropertyAssignment(constraintProp)) {
          continue;
        }

        const propName = nameText(constraintProp);
        const propValue = constraintProp.initializer;
        if (!propValue) {
          continue;
        }

        if (propName === "requires" && isStringLiteral(propValue)) {
          requires = propValue.text;
        } else if (propName === "ensures" && isStringLiteral(propValue)) {
          ensures = propValue.text;
        } else if (propName === "message" && isStringLiteral(propValue)) {
          message = propValue.text;
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
          line: startLine(property),
        },
      });
    }

    return results;
  }

  // Verified State Discovery (Issue #27)

  /**
   * Extract $sharedState declarations with { verify: true } from a source file
   *
   * Finds patterns like:
   *   const authState = $sharedState('auth', initialState, { verify: true })
   *   export const settings = $syncedState('settings', defaults, { verify: true })
   */
  extractVerifiedStatesFromFile(sourceFile: SourceFile): VerifiedStateInfo[] {
    const verifiedStates: VerifiedStateInfo[] = [];
    const filePath = sourceFile.fileName;

    forEachDescendant(sourceFile, (node) => {
      if (!isCallExpression(node)) return;

      const stateInfo = this.recognizeVerifiedStateCall(node, filePath);
      if (stateInfo) {
        verifiedStates.push(stateInfo);
      }
    });

    return verifiedStates;
  }

  /**
   * Recognize a $sharedState/$syncedState/$persistedState call with verify: true
   */
  private recognizeVerifiedStateCall(node: Node, filePath: string): VerifiedStateInfo | null {
    if (!isCallExpression(node)) return null;

    const expression = node.expression;
    if (!isIdentifier(expression)) return null;

    const funcName = textOf(expression);
    // Match state primitives that support verification
    if (!["$sharedState", "$syncedState", "$persistedState"].includes(funcName)) {
      return null;
    }

    const args = node.arguments;
    if (args.length < 2) return null;

    // Check for { verify: true } in options (3rd argument)
    const optionsArg = args[2];
    if (!optionsArg || !this.hasVerifyTrue(optionsArg)) return null;

    // Extract state key (1st argument)
    const keyArg = args[0];
    if (!keyArg || !isStringLiteral(keyArg)) return null;
    const key = keyArg.text;

    // Get variable name from parent declaration
    const variableName = this.getVariableNameFromParent(node) || key;

    // Extract field names from initial value (2nd argument)
    const initialValueArg = args[1];
    const fields = initialValueArg ? this.extractFieldNames(initialValueArg) : [];

    if (process.env["POLLY_DEBUG"]) {
      console.log(
        `[DEBUG] Found verified state: ${variableName} (key: "${key}") with fields: [${fields.join(", ")}]`
      );
    }

    return {
      key,
      variableName,
      filePath,
      line: startLine(node),
      fields,
    };
  }

  /**
   * Check if an options object contains verify: true
   */
  private hasVerifyTrue(optionsNode: Node): boolean {
    if (!isObjectLiteralExpression(optionsNode)) return false;

    for (const prop of optionsNode.properties) {
      if (!isPropertyAssignment(prop)) continue;

      const name = nameText(prop);
      if (name !== "verify") continue;

      const initializer = prop.initializer;
      if (initializer && initializer.kind === SyntaxKind.TrueKeyword) {
        return true;
      }
    }

    return false;
  }

  /**
   * Get variable name from parent VariableDeclaration
   */
  private getVariableNameFromParent(node: Node): string | null {
    const parent = node.parent;
    if (isVariableDeclaration(parent)) {
      return nameText(parent);
    }
    return null;
  }

  /**
   * Extract field names from an initial value expression
   * Handles object literals and identifier references
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Field extraction requires traversing nested object structures
  private extractFieldNames(node: Node): string[] {
    const fields: string[] = [];

    if (isObjectLiteralExpression(node)) {
      for (const prop of node.properties) {
        if (isPropertyAssignment(prop) || isShorthandPropertyAssignment(prop)) {
          fields.push(nameText(prop));
        }
      }
    } else if (isIdentifier(node)) {
      // Try to resolve the identifier to its declaration
      const definitions = this.definitionsOf(node);
      for (const def of definitions) {
        if (isVariableDeclaration(def)) {
          const initializer = def.initializer;
          if (initializer && isObjectLiteralExpression(initializer)) {
            return this.extractFieldNames(initializer);
          }
        }
      }
    }

    return fields;
  }

  /**
   * Find exported functions that modify verified state signals
   *
   * Looks for patterns:
   *   - authState.value = { ... }
   *   - authState.value.field = value
   */
  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: State mutation detection requires complex AST pattern matching
  async findStateMutatingFunctions(
    sourceFile: SourceFile,
    verifiedStates: VerifiedStateInfo[]
  ): Promise<MessageHandler[]> {
    const handlers: MessageHandler[] = [];
    const stateVarNames = new Set(verifiedStates.map((s) => s.variableName));
    const filePath = sourceFile.fileName;
    const context = this.inferContext(filePath);

    // Find all exported functions (`export { f }` counts, so ask the checker)
    const functions = functionDeclarations(sourceFile);
    const exported = await Promise.all(functions.map((func) => this.program.isExported(func)));
    for (const [index, func] of functions.entries()) {
      if (!exported[index]) continue;

      const funcName = nameOf(func);
      if (!funcName) continue;

      // Check if function modifies any verified state
      this.currentFunctionParams = this.extractParameterNames(func);
      const assignments = this.findStateMutationsInFunction(func, stateVarNames);
      if (assignments.length === 0) {
        this.currentFunctionParams = [];
        continue;
      }

      // Extract requires/ensures
      const preconditions: VerificationCondition[] = [];
      const postconditions: VerificationCondition[] = [];
      this.extractVerificationConditions(func, preconditions, postconditions);

      // Generate message type from function name
      const messageType = this.functionNameToMessageType(funcName);

      const parameters =
        this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
      this.currentFunctionParams = [];

      if (process.env["POLLY_DEBUG"]) {
        console.log(
          `[DEBUG] Found state-mutating function: ${funcName} → ${messageType} ` +
            `(${assignments.length} assignments, ${preconditions.length} preconditions, ${postconditions.length} postconditions)`
        );
      }

      handlers.push({
        messageType,
        node: context,
        assignments,
        preconditions,
        postconditions,
        location: {
          file: filePath,
          line: startLine(func),
        },
        origin: "stateHandler" as const,
        parameters,
      });
    }

    // Also check exported variable declarations with arrow functions
    for (const varStmt of variableStatements(sourceFile)) {
      if (!hasExportKeyword(varStmt)) continue;

      for (const decl of varStmt.declarationList.declarations) {
        const initializer = decl.initializer;
        if (!initializer) continue;
        if (!isArrowFunction(initializer) && !isFunctionExpression(initializer)) continue;

        const funcName = nameText(decl);
        if (!funcName) continue;

        this.currentFunctionParams = this.extractParameterNames(initializer);
        const assignments = this.findStateMutationsInFunction(initializer, stateVarNames);
        if (assignments.length === 0) {
          this.currentFunctionParams = [];
          continue;
        }

        const preconditions: VerificationCondition[] = [];
        const postconditions: VerificationCondition[] = [];
        this.extractVerificationConditions(initializer, preconditions, postconditions);

        const messageType = this.functionNameToMessageType(funcName);

        const arrowParams =
          this.currentFunctionParams.length > 0 ? [...this.currentFunctionParams] : undefined;
        this.currentFunctionParams = [];

        if (process.env["POLLY_DEBUG"]) {
          console.log(`[DEBUG] Found state-mutating arrow function: ${funcName} → ${messageType}`);
        }

        handlers.push({
          messageType,
          node: context,
          assignments,
          preconditions,
          postconditions,
          location: {
            file: filePath,
            line: startLine(decl),
          },
          origin: "stateHandler" as const,
          parameters: arrowParams,
        });
      }
    }

    return handlers;
  }

  /**
   * True when `node` sits in a callback passed to `.on(...)` /
   * `.addEventListener(...)` somewhere below `func`.
   */
  private isInsideHandlerRegistration(node: Node, func: Node): boolean {
    let current: Node | undefined = node.parent;
    while (current && current !== func) {
      if (isCallExpression(current)) {
        const callee = current.expression;
        if (
          isPropertyAccessExpression(callee) &&
          (nameText(callee) === "on" || nameText(callee) === "addEventListener")
        ) {
          return true;
        }
      }
      current = current.parent;
    }
    return false;
  }

  /**
   * Find state mutations within a function that target verified state signals
   */
  private findStateMutationsInFunction(
    func: FunctionDeclaration | ArrowFunction | FunctionExpression,
    stateVarNames: Set<string>
  ): StateAssignment[] {
    const mutations: StateAssignment[] = [];

    // polly#163: the Issue #27 lift pass models this exported mutator's body as
    // a synthetic handler, so writes within it are on-surface.
    this.recordOnSurfaceSpan(func);

    // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: AST traversal for state mutations requires multiple pattern checks
    forEachDescendant(func, (node) => {
      if (!isBinaryExpression(node)) return;

      const operator = textOf(node.operatorToken);
      if (operator !== "=") return;

      // A write inside a `bus.on(...)` callback registered by this function is
      // that handler's write, already modelled by the dispatch extraction. A
      // `registerHandlers(bus)` composite helper must not become a handler of
      // its own that replays every nested write unguarded.
      if (this.isInsideHandlerRegistration(node, func)) return;

      const left = node.left;
      if (!isPropertyAccessExpression(left)) return;

      const path = this.getPropertyPath(left);

      // Check for patterns:
      // 1. authState.value = { ... }  (full replacement)
      // 2. authState.value.field = value  (field update)
      for (const varName of stateVarNames) {
        // Pattern 1: Full state replacement
        // e.g., authState.value = { loggedIn: true } → authState_loggedIn = true
        if (path === `${varName}.value`) {
          const right = node.right;
          if (isObjectLiteralExpression(right)) {
            this.extractObjectLiteralAssignments(right, mutations, varName);
          }
          break;
        }

        // Pattern 2: Field update
        // e.g., authState.value.loggedIn = true → authState_loggedIn = true
        const fieldPrefix = `${varName}.value.`;
        if (path.startsWith(fieldPrefix)) {
          const fieldName = path.substring(fieldPrefix.length);
          const value = this.extractValue(node.right);
          mutations.push({ field: `${varName}_${fieldName}`, value: value ?? "@" });
          break;
        }
      }
    });

    return mutations;
  }

  // polly#163: off-surface mutator detection

  /**
   * Whether a file is application source the off-surface scan should cover.
   * Test, spec, BDD-feature, story and e2e files seed verified state directly
   * as fixtures — expected, not an escaped runtime mutator — so they are out.
   */
  private isOffSurfaceScannable(filePath: string): boolean {
    return !isOffSurfacePath(filePath);
  }

  /** The signal factories whose `.value` writes the model treats as state. */
  private static readonly STATE_SIGNAL_FACTORIES = new Set([
    "$state",
    "$sharedState",
    "$syncedState",
    "$persistedState",
    "$meshState",
    "$peerState",
  ]);

  /**
   * Collect the variable names of every state-signal declaration in a file,
   * regardless of a `{ verify: true }` flag. Scopes the off-surface scan to
   * genuine state signals so it does not false-positive on unrelated `.value`
   * writes.
   */
  private extractStateSignalVariableNames(sourceFile: SourceFile): string[] {
    const names: string[] = [];
    forEachDescendant(sourceFile, (node) => {
      if (!isCallExpression(node)) return;
      const expr = node.expression;
      if (!isIdentifier(expr)) return;
      if (!HandlerExtractor.STATE_SIGNAL_FACTORIES.has(textOf(expr))) return;
      const varName = this.getVariableNameFromParent(node);
      if (varName) names.push(varName);
    });
    return names;
  }

  /**
   * Mark a function body as part of the modelled handler surface. Called from
   * the two extraction chokepoints — `extractAssignments` (every dispatch / ws /
   * rest / type-guard / switch handler body) and `findStateMutationsInFunction`
   * (every lifted exported mutator). A verified-state write whose position is
   * not contained in any recorded span is off-surface.
   */
  private recordOnSurfaceSpan(node: Node): void {
    this.onSurfaceSpans.push({
      file: node.getSourceFile().fileName,
      start: startOf(node),
      end: node.end,
    });
  }

  /** True when `pos` in `file` falls inside a modelled handler body span. */
  private isWithinOnSurfaceSpan(file: string, pos: number): boolean {
    for (const span of this.onSurfaceSpans) {
      if (span.file === file && pos >= span.start && pos <= span.end) return true;
    }
    return false;
  }

  /**
   * Walk a file for verified-state writes (`signal.value` / `signal.value.field`
   * on the left of `=`) that are NOT inside any modelled handler body. These are
   * the escaped, non-dispatched mutators of polly#163 — the model never explores
   * them, so a field only they (or they-and-a-handler) write is silently
   * uncounted by the #162 coverage report.
   *
   * Must run after all handler extraction so `onSurfaceSpans` is complete.
   */
  private findOffSurfaceMutations(
    sourceFile: SourceFile,
    stateVarNames: ReadonlySet<string>
  ): OffSurfaceMutation[] {
    const out: OffSurfaceMutation[] = [];
    const filePath = sourceFile.fileName;

    forEachDescendant(sourceFile, (node) => {
      if (isBinaryExpression(node)) {
        out.push(...this.offSurfaceWritesAt(node, stateVarNames, filePath));
      }
    });

    return out;
  }

  /**
   * Off-surface findings for a single assignment node, or `[]` when it is not a
   * verified-state write or is inside a modelled handler body.
   */
  private offSurfaceWritesAt(
    node: BinaryExpression,
    stateVarNames: ReadonlySet<string>,
    filePath: string
  ): OffSurfaceMutation[] {
    if (textOf(node.operatorToken) !== "=") return [];

    const left = node.left;
    if (!isPropertyAccessExpression(left)) return [];

    const match = this.matchVerifiedStateWrite(this.getPropertyPath(left), stateVarNames);
    if (!match) return [];

    // On-surface writes belong to a modelled handler — skip them.
    if (this.isWithinOnSurfaceSpan(filePath, startOf(left))) return [];

    const base = {
      signalVariable: match.signal,
      functionName: this.enclosingFunctionName(node),
      filePath,
      line: startLine(node),
    };

    // Field-level write: one finding, keyed `${signal}_${field}`.
    if (match.field !== undefined) {
      return [{ field: `${match.signal}_${match.field}`, ...base }];
    }

    // Whole-state replacement: one finding per object-literal key, or the bare
    // signal name when the RHS is not an object literal.
    const fields = this.objectLiteralFieldNames(node.right);
    if (fields.length === 0) return [{ field: match.signal, ...base }];
    return fields.map((f) => ({ field: `${match.signal}_${f}`, ...base }));
  }

  /**
   * Recognize `signal.value` (whole-state) or `signal.value.field` (field) on
   * the LHS of an assignment, where `signal` is a verified-state variable.
   * Mirrors the two patterns in `findStateMutationsInFunction`.
   */
  private matchVerifiedStateWrite(
    path: string,
    stateVarNames: ReadonlySet<string>
  ): { signal: string; field?: string } | null {
    for (const varName of stateVarNames) {
      if (path === `${varName}.value`) return { signal: varName };
      const prefix = `${varName}.value.`;
      if (path.startsWith(prefix)) return { signal: varName, field: path.substring(prefix.length) };
    }
    return null;
  }

  /** Object-literal property names (for `signal.value = { a, b }`). */
  private objectLiteralFieldNames(right: Node): string[] {
    if (!isObjectLiteralExpression(right)) return [];
    const names: string[] = [];
    for (const prop of right.properties) {
      if (isPropertyAssignment(prop) || isShorthandPropertyAssignment(prop)) {
        names.push(nameText(prop));
      }
    }
    return names;
  }

  /**
   * Name the nearest enclosing function/method of a node for the off-surface
   * report: `Class.method`, a bare function/accessor name, the variable a
   * function expression is bound to, or `<module>` for top-level module code.
   */
  private enclosingFunctionName(node: Node): string {
    let current: Node | undefined = node.parent;
    while (current) {
      const name = this.namedScope(current);
      if (name !== null) return name;
      current = current.parent;
    }
    return "<module>";
  }

  /**
   * The display name of a function-like node, or `null` when `node` is not a
   * function-like scope (keep climbing) or is an unnamed closure (keep climbing
   * to the nearest named scope).
   */
  private namedScope(node: Node): string | null {
    if (isFunctionDeclaration(node)) {
      return nameOf(node) ?? "<anonymous function>";
    }
    if (isMethodDeclaration(node)) {
      const cls = firstAncestor(node, isClassDeclaration);
      const clsName = cls ? nameOf(cls) : undefined;
      const methodName = nameText(node);
      return clsName ? `${clsName}.${methodName}` : methodName;
    }
    if (isGetAccessorDeclaration(node) || isSetAccessorDeclaration(node)) {
      return nameText(node);
    }
    if (isArrowFunction(node) || isFunctionExpression(node)) {
      return this.boundFunctionName(node) ?? null;
    }
    return null;
  }

  /** The variable / property name a function expression is assigned to, if any. */
  private boundFunctionName(fn: Node): string | undefined {
    const parent = fn.parent;
    if (!parent) return undefined;
    if (isVariableDeclaration(parent)) return nameText(parent);
    if (isPropertyAssignment(parent)) return nameText(parent);
    return undefined;
  }

  /**
   * Convert function name to message type
   * Examples:
   *   handleAuthSuccess → AuthSuccess
   *   handleLogout → Logout
   *   setUserProfile → SetUserProfile
   */
  private functionNameToMessageType(funcName: string): string {
    // Remove common handler prefixes
    let name = funcName
      .replace(/^handle/, "")
      .replace(/^on/, "")
      .replace(/^set/, "Set")
      .replace(/^update/, "Update")
      .replace(/^do/, "");

    // Ensure first letter is uppercase
    if (name.length > 0) {
      name = name.charAt(0).toUpperCase() + name.slice(1);
    }

    return name || funcName;
  }

  // $resource() Discovery

  /**
   * Extract $resource() calls from a source file.
   *
   * Recognizes: const todos = $resource("todos", { source, fetcher, initialValue })
   */
  private extractResourcesFromFile(sourceFile: SourceFile, filePath: string): ResourceInfo[] {
    const resources: ResourceInfo[] = [];

    forEachDescendant(sourceFile, (node) => {
      if (!isCallExpression(node)) return;

      const resource = this.extractResourcePattern(node, filePath);
      if (resource) {
        resources.push(resource);
      }
    });

    return resources;
  }

  /**
   * Match a $resource() call and extract its metadata.
   */
  private extractResourcePattern(node: CallExpression, filePath: string): ResourceInfo | null {
    const expression = node.expression;
    if (!isIdentifier(expression)) return null;
    if (textOf(expression) !== "$resource") return null;

    const args = node.arguments;
    if (args.length < 2) return null;

    // First arg: resource name (string literal)
    const nameArg = args[0];
    if (!nameArg || !isStringLiteral(nameArg)) return null;
    const name = nameArg.text;

    // Second arg: options object with source, fetcher, initialValue
    const optionsArg = args[1];
    if (!optionsArg || !isObjectLiteralExpression(optionsArg)) return null;

    // Extract source signal reads
    const sourceSignals = this.extractResourceSourceReads(optionsArg);

    // Get variable name from parent declaration
    const variableName = this.getVariableNameFromParent(node) || name;

    if (process.env["POLLY_DEBUG"]) {
      console.log(
        `[DEBUG] Found $resource: ${variableName} (name: "${name}") with source signals: [${sourceSignals.join(", ")}]`
      );
    }

    return {
      name,
      variableName,
      filePath,
      line: startLine(node),
      sourceSignals,
    };
  }

  /**
   * Walk the source() function in a $resource options object to find .value reads.
   *
   * Looks for patterns like:
   *   source: () => ({ userId: authState.value.userId })
   * Extracts signal field names: ["authState_userId"]
   */
  private extractResourceSourceReads(optionsObj: ObjectLiteralExpression): string[] {
    const signals: string[] = [];

    const sourceProp = objectProperty(optionsObj, "source");
    if (!sourceProp || !isPropertyAssignment(sourceProp)) return signals;

    const sourceInit = sourceProp.initializer;
    if (!sourceInit) return signals;

    // Walk the source function body looking for .value reads
    forEachDescendant(sourceInit, (node) => {
      if (!isPropertyAccessExpression(node)) return;

      const text = textOf(node);
      // Match: signal.value.field or signal.value
      const match = text.match(/^(\w+)\.value(?:\.(\w+))?$/);
      if (match) {
        const signalName = match[1];
        const fieldName = match[2];
        if (!signalName) return;
        if (fieldName) {
          signals.push(`${signalName}_${fieldName}`);
        } else {
          signals.push(signalName);
        }
      }
    });

    return signals;
  }

  /**
   * Create three synthetic MessageHandler entries for a $resource:
   *   - {name}_FetchStart: source available, status != loading → status = loading
   *   - {name}_FetchSuccess: status == loading → status = success, error = false
   *   - {name}_FetchError: status == loading → status = error, error = true
   */
  private createResourceHandlers(resource: ResourceInfo, context: string): MessageHandler[] {
    const { name, filePath, line } = resource;
    const location = { file: filePath, line };

    const fetchStart: MessageHandler = {
      messageType: `${name}_FetchStart`,
      node: context,
      assignments: [
        { field: `${name}_status`, value: "loading" },
        { field: `${name}_error`, value: false },
      ],
      preconditions: [
        {
          expression: `${name}_status !== "loading"`,
          location: { line, column: 0 },
        },
      ],
      postconditions: [],
      location,
    };

    const fetchSuccess: MessageHandler = {
      messageType: `${name}_FetchSuccess`,
      node: context,
      assignments: [
        { field: `${name}_status`, value: "success" },
        { field: `${name}_error`, value: false },
      ],
      preconditions: [
        {
          expression: `${name}_status === "loading"`,
          location: { line, column: 0 },
        },
      ],
      postconditions: [],
      location,
    };

    const fetchError: MessageHandler = {
      messageType: `${name}_FetchError`,
      node: context,
      assignments: [
        { field: `${name}_status`, value: "error" },
        { field: `${name}_error`, value: true },
      ],
      preconditions: [
        {
          expression: `${name}_status === "loading"`,
          location: { line, column: 0 },
        },
      ],
      postconditions: [],
      location,
    };

    return [fetchStart, fetchSuccess, fetchError];
  }
}

export function extractHandlers(
  tsConfigPath: string,
  source?: AnalysisSource
): Promise<HandlerAnalysis> {
  const extractor = new HandlerExtractor(tsConfigPath);
  return extractor.extractHandlers(source);
}
