// The typescript-7 program the extractors run on, in place of ts-morph.
//
// One `AnalysisSession` owns one tsgo process for a CLI run; `open(tsconfig)`
// loads a project once and hands every extractor the same `AnalysisProgram`.
// The session MUST be closed (`await session.close()`, `await using`, or
// `withAnalysisSession`): an open API keeps Bun and Node alive forever.
//
// Split by cost:
//  - AST helpers (./ast.ts) are synchronous: a fetched SourceFile is a local tree.
//  - Checker helpers here are async: each is one IPC round trip (~35 µs on
//    Bun), batched per tick by the client, so issue independent calls together.
//  - `prefetchDefinitions` / `prefetchImports` resolve the few checker facts
//    the AST-only extractors need up front, so their lookups stay synchronous.
//
// Each helper names the ts-morph method it replaces and reproduces its answer;
// the exceptions are listed on the helper (see also __tests__/).

import { existsSync } from "node:fs";
import { resolve } from "node:path";
import type {
  CallExpression,
  Declaration,
  FunctionDeclaration,
  Identifier,
  ImportDeclaration,
  NewExpression,
  Node,
  PathKey,
  SourceFile,
  VariableStatement,
} from "typescript-7/ast";
import { SyntaxKind } from "typescript-7/ast";
import {
  isArrowFunction,
  isCallExpression,
  isCallSignatureDeclaration,
  isConstructorDeclaration,
  isConstructSignatureDeclaration,
  isFunctionDeclaration,
  isFunctionExpression,
  isGetAccessorDeclaration,
  isIdentifier,
  isMethodDeclaration,
  isMethodSignatureDeclaration,
  isNewExpression,
  isPropertyAssignment,
  isPropertyDeclaration,
  isSetAccessorDeclaration,
  isTypeAliasDeclaration,
  isVariableDeclaration,
} from "typescript-7/ast/is";
import {
  API,
  type Checker,
  type CompilerOptions,
  type NodeHandle,
  type Program,
  type Project,
  type Snapshot,
  SymbolFlags,
  type Symbol as TsSymbol,
  type Type,
  TypeFormatFlags,
} from "typescript-7/async";
import { forEachDescendant, hasExportKeyword, importDeclarations } from "./ast";
import { createSourceGlob } from "./glob";
import { typeIs, typeLiteralValue } from "./type-flags";

/** ts-morph's default `Type.getText()` flags (TypeChecker#getDefaultTypeFormatFlags). */
export const MORPH_TYPE_FORMAT =
  TypeFormatFlags.UseTypeOfFunction |
  TypeFormatFlags.NoTruncation |
  TypeFormatFlags.UseFullyQualifiedType |
  TypeFormatFlags.WriteTypeArgumentsOfSignature;

/** A property of a type, as types.ts and contexts.ts read it. */
export interface PropertyInfo {
  name: string;
  symbol: TsSymbol;
  /** ts-morph `prop.getTypeAtLocation(at)`. */
  type: Type;
}

function compareFilePaths(a: string, b: string): number {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

/** The identifiers `prefetchDefinitions` resolves by default: everything the extractors look up. */
export function isDefinitionSite(node: Node): node is Identifier {
  if (!isIdentifier(node)) return false;
  const parent = node.parent;
  if (isCallExpression(parent) || isNewExpression(parent)) {
    return parent.expression === node || (parent.arguments?.includes(node) ?? false);
  }
  return isPropertyAssignment(parent) && parent.initializer === node;
}

/** One project of the session: the files, the checker, and ts-morph-shaped helpers over them. */
export class AnalysisProgram {
  readonly tsconfig: string;
  readonly project: Project;
  readonly program: Program;
  readonly checker: Checker;
  /**
   * ts-morph `project.getSourceFiles()`: every program file outside
   * node_modules (default libs included in neither), sorted by absolute path.
   */
  readonly sourceFiles: readonly SourceFile[];

  private readonly byFileName: ReadonlyMap<string, SourceFile>;
  private readonly byPath: ReadonlyMap<PathKey, SourceFile>;
  /** Files outside `sourceFiles` fetched for a declaration lookup, by path. */
  private readonly external = new Map<PathKey, Promise<SourceFile | undefined>>();
  private readonly definitions = new Map<Node, readonly Declaration[]>();
  private readonly importTargets = new Map<Node, SourceFile | undefined>();
  private defaultDefinitions: Promise<void> | undefined;
  private imports: Promise<void> | undefined;

  private constructor(tsconfig: string, project: Project, sourceFiles: readonly SourceFile[]) {
    this.tsconfig = tsconfig;
    this.project = project;
    this.program = project.program;
    this.checker = project.checker;
    this.sourceFiles = sourceFiles;
    this.byFileName = new Map(sourceFiles.map((file) => [file.fileName, file]));
    this.byPath = new Map(sourceFiles.map((file) => [file.path, file]));
  }

  /** @internal Built by `AnalysisSession.open`. */
  static async load(tsconfig: string, project: Project): Promise<AnalysisProgram> {
    const names = (await project.program.getSourceFileNames()).filter(
      (name) => !name.includes("/node_modules/")
    );
    const files = await Promise.all(names.map((name) => project.program.getSourceFile(name)));
    const sourceFiles = files
      .filter((file): file is SourceFile => file !== undefined)
      .sort((a, b) => compareFilePaths(a.fileName, b.fileName));
    return new AnalysisProgram(tsconfig, project, sourceFiles);
  }

  // ---------------------------------------------------------------- files

  /**
   * ts-morph `project.getSourceFile(path)`: a path (anything with a `/`) is
   * resolved against the cwd and looked up exactly; a bare file name matches
   * the first file (in path order) whose path ends with `/<name>`.
   */
  sourceFile(fileNameOrPath: string): SourceFile | undefined {
    if (fileNameOrPath.includes("/")) return this.byFileName.get(resolve(fileNameOrPath));
    return this.sourceFiles.find((file) => file.fileName.endsWith(`/${fileNameOrPath}`));
  }

  /**
   * ts-morph `project.getSourceFiles(glob)`: the glob is joined onto `cwd`
   * (ts-morph uses the process cwd) and matched with minimatch's defaults,
   * so `**` never enters a dot directory. Path order, like `sourceFiles`.
   */
  sourceFilesMatching(glob: string, cwd: string = process.cwd()): SourceFile[] {
    const matches = createSourceGlob(glob, cwd);
    return this.sourceFiles.filter((file) => matches(file.fileName));
  }

  /** ts-morph `project.getCompilerOptions()`; `configFilePath` is present. */
  get compilerOptions(): CompilerOptions {
    return this.program.getCompilerOptions();
  }

  // ---------------------------------------------------------------- checker

  /** ts-morph `node.getType()`. */
  typeOf(node: Node): Promise<Type> {
    return this.checker.getTypeAtLocation(node);
  }

  /** ts-morph `type.getText(enclosing?)`: its default flags, plus InTypeAlias inside a type alias. */
  typeText(type: Type, enclosing?: Node): Promise<string> {
    const flags =
      enclosing && isTypeAliasDeclaration(enclosing)
        ? MORPH_TYPE_FORMAT | TypeFormatFlags.InTypeAlias
        : MORPH_TYPE_FORMAT;
    return this.checker.typeToString(type, enclosing, flags);
  }

  /**
   * ts-morph `type.getUnionTypes()` ([] for a non-union).
   *
   * PARITY: TS 6 kept a union's members in type-id order, which is the
   * order the checker created them; TS 7 orders literal members by value.
   * TS 7 still numbers types in creation order, so sorting by id restores
   * the TS 6 order — measured on every union reachable from the aliases of
   * polly, full-featured, todo-list and the types corpus: 864 of 885 (the
   * rest differ only in noise the comparison could not normalise, or are a
   * literal TS 7 happened to create earlier than TS 6 did, as with `"md"` in
   * polly-ui's Radius/Shadow/TextSize). One fixed exception: both checkers
   * pre-create the `typeof` result literals ("string", "number", …) at start
   * up, TS 6 in typeof order and TS 7 alphabetically, so those are put back
   * in TS 6's order. Creation order depends on what was asked before: open
   * the program with `openIsolated` for an extractor whose output follows
   * union order (types.ts), as ts-morph gave each extractor its own Project.
   */
  async unionMembers(type: Type): Promise<readonly Type[]> {
    if (!type.isUnionType()) return [];
    const members = [...(await type.getTypes())].sort((a, b) => a.id - b.id);
    const slots: number[] = [];
    const typeofLiterals: Type[] = [];
    members.forEach((member, index) => {
      if (typeofRank(member) !== undefined) {
        slots.push(index);
        typeofLiterals.push(member);
      }
    });
    typeofLiterals.sort((a, b) => (typeofRank(a) ?? 0) - (typeofRank(b) ?? 0));
    slots.forEach((slot, i) => {
      const literal = typeofLiterals[i];
      if (literal) members[slot] = literal;
    });
    return members;
  }

  /** ts-morph `type.isNullable()`: a union with a null or undefined member. */
  async isNullable(type: Type): Promise<boolean> {
    if (!type.isUnionType()) return false;
    const members = await type.getTypes();
    return members.some((member) => typeIs.null(member) || typeIs.undefined(member));
  }

  /** ts-morph `type.getTypeArguments()` ([] unless the type is a type reference). */
  async typeArguments(type: Type): Promise<readonly Type[]> {
    return type.isTypeReference() ? this.checker.getTypeArguments(type) : [];
  }

  /** ts-morph `type.getArrayElementType()`: `Array` or `ReadonlyArray` with one type argument (ts-morph's `isArray()`). */
  async arrayElement(type: Type): Promise<Type | undefined> {
    const symbol = await type.getSymbol();
    if (symbol?.name !== "Array" && symbol?.name !== "ReadonlyArray") return undefined;
    const args = await this.typeArguments(type);
    return args.length === 1 ? args[0] : undefined;
  }

  /**
   * ts-morph `type.getProperties()`, each with `prop.getTypeAtLocation(at)`.
   *
   * PARITY: a mapped type's properties come in its key union's order, which
   * TS 7 sorts by value; they are put back in `unionMembers` order, as TS 6
   * listed them. Not reproduced: properties of default-library types (Map,
   * Date, …) follow TS 7's own lib files, and well-known-symbol members are
   * named `__@iterator@<id>` with a TS 7 symbol id.
   */
  async properties(type: Type, at: Node): Promise<PropertyInfo[]> {
    return this.describeProperties(await this.propertySymbols(type), at);
  }

  /** ts-morph `type.getProperties().map((p) => p.getName())`. */
  async propertyNames(type: Type): Promise<string[]> {
    return (await this.propertySymbols(type)).map((symbol) => symbol.name);
  }

  /** ts-morph `symbol.getTypeAtLocation(at)`. */
  symbolTypeAt(symbol: TsSymbol, at: Node): Promise<Type> {
    return this.checker.getTypeOfSymbolAtLocation(symbol, at);
  }

  /** ts-morph `type.getProperty(name)`, with `getTypeAtLocation(at)`. */
  async property(type: Type, name: string, at: Node): Promise<PropertyInfo | undefined> {
    const symbols = await this.propertySymbols(type);
    const symbol = symbols.find((candidate) => candidate.name === name);
    return symbol ? (await this.describeProperties([symbol], at))[0] : undefined;
  }

  /**
   * ts-morph `type.getProperties()`: the property symbols, mapped-type
   * properties in `unionMembers` order of their keys (see `properties`).
   */
  async propertySymbols(type: Type): Promise<readonly TsSymbol[]> {
    const symbols = await this.checker.getPropertiesOfType(type);
    if (!type.isMappedType()) return symbols;
    const constraint = await type.getConstraintType();
    const keys = constraint.isUnionType() ? await this.unionMembers(constraint) : [constraint];
    const rank = new Map<string, number>();
    keys.forEach((key, i) => {
      const value = typeLiteralValue(key);
      if (value !== undefined && !rank.has(String(value))) rank.set(String(value), i);
    });
    const unranked = keys.length;
    return symbols
      .map((symbol, index) => ({ symbol, index, rank: rank.get(symbol.name) ?? unranked }))
      .sort((a, b) => a.rank - b.rank || a.index - b.index)
      .map((entry) => entry.symbol);
  }

  private async describeProperties(
    symbols: readonly TsSymbol[],
    at: Node
  ): Promise<PropertyInfo[]> {
    const types = await Promise.all(
      symbols.map((symbol) => this.checker.getTypeOfSymbolAtLocation(symbol, at))
    );
    return symbols.map((symbol, i) => {
      const type = types[i];
      if (!type) throw new Error(`no type for property ${symbol.name}`);
      return { name: symbol.name, symbol, type };
    });
  }

  /** ts-morph `type.getAliasSymbol()?.getDeclaredType()`. */
  async aliasDeclaredType(type: Type): Promise<Type | undefined> {
    const alias = await type.getAliasSymbol();
    return alias ? this.checker.getDeclaredTypeOfSymbol(alias) : undefined;
  }

  /** ts-morph `fn.getReturnType()`. */
  async returnType(fn: Node): Promise<Type> {
    return this.checker.getReturnTypeOfSignature(
      await this.checker.getSignatureFromDeclaration(fn)
    );
  }

  /**
   * ts-morph `isExported()`: an `export` keyword, or (for a function) a file
   * export that is, or aliases, the declaration's symbol (`export { f }`,
   * `export default f`). A variable statement has no symbol, so only its
   * keyword counts, as in ts-morph.
   */
  async isExported(declaration: FunctionDeclaration | VariableStatement): Promise<boolean> {
    if (hasExportKeyword(declaration)) return true;
    if (!isFunctionDeclaration(declaration)) return false;
    const [own, file] = await Promise.all([
      this.checker.getSymbolOfDeclaration(declaration),
      this.checker.getSymbolOfSourceFile(declaration.getSourceFile().fileName),
    ]);
    if (!file) return false;
    const exports = [...(await file.getExports()).values()];
    if (exports.some((symbol) => symbol.id === own.id)) return true;
    const aliased = await Promise.all(
      exports
        .filter((symbol) => symbol.flags & SymbolFlags.Alias)
        .map((symbol) => this.checker.getAliasedSymbol(symbol))
    );
    return aliased.some((symbol) => symbol.id === own.id);
  }

  // ---------------------------------------------------------------- declarations

  /**
   * Resolve declaration handles to nodes. Each file a handle points into is
   * fetched once first: resolving handles concurrently into an unfetched file
   * re-fetches the whole file per handle (measured: 44 Date members, 136 ms
   * cold vs 5 ms with the file fetched first; a whole-program definition pass
   * took 18 s and 4.8 GB).
   */
  async resolveDeclarations(handles: readonly NodeHandle<Declaration>[]): Promise<Declaration[]> {
    const nodes = await this.resolveEach(handles);
    return nodes.filter((node): node is Declaration => node !== undefined);
  }

  private async resolveEach(
    handles: readonly (NodeHandle<Declaration> | undefined)[]
  ): Promise<(Declaration | undefined)[]> {
    await Promise.all(handles.map((handle) => (handle ? this.fileAtPath(handle.path) : undefined)));
    return Promise.all(handles.map((handle) => handle?.resolve(this.project)));
  }

  private fileAtPath(path: PathKey): Promise<SourceFile | undefined> | SourceFile | undefined {
    const own = this.byPath.get(path);
    if (own) return own;
    let pending = this.external.get(path);
    if (!pending) {
      pending = this.program.getSourceFileByPath(path);
      this.external.set(path, pending);
    }
    return pending;
  }

  // ---------------------------------------------------------------- prefetch

  /**
   * Resolve go-to-definition for identifiers in one batched pass, so
   * `definitionNodes` can answer synchronously. With no argument it covers
   * every `isDefinitionSite` identifier in `sourceFiles` (call callees, call
   * and `new` arguments, property-assignment values) and runs once; pass
   * other identifiers to add them.
   *
   * PARITY with ts-morph `getDefinitionNodes()` (language-service
   * go-to-definition): the symbol's declarations, imports followed to the
   * aliased declaration; for a callee, the language service's signature rule
   * too — when the call resolved to one of those declarations (an overload,
   * or the arrow function a `const` holds) only that one is returned, and
   * otherwise it is appended (`const { f } = await import("./x"); f()` →
   * the BindingElement and `f`'s declaration in x). Declarations in default
   * library files are returned too, but ts-morph reads its own bundled TS 6
   * libs, so those nodes differ from ts-morph's by construction.
   */
  prefetchDefinitions(identifiers?: Iterable<Identifier>): Promise<void> {
    if (identifiers)
      return this.resolveDefinitions([...identifiers].filter((id) => !this.definitions.has(id)));
    if (!this.defaultDefinitions) {
      const ids: Identifier[] = [];
      for (const file of this.sourceFiles) {
        forEachDescendant(file, (node) => {
          if (isDefinitionSite(node)) ids.push(node);
        });
      }
      this.defaultDefinitions = this.resolveDefinitions(
        ids.filter((id) => !this.definitions.has(id))
      );
    }
    return this.defaultDefinitions;
  }

  private async resolveDefinitions(ids: readonly Identifier[]): Promise<void> {
    if (ids.length === 0) return;
    const symbols = await this.checker.getSymbolAtLocation(ids);
    const targets = await Promise.all(
      symbols.map((symbol) =>
        symbol && symbol.flags & SymbolFlags.Alias ? this.checker.getAliasedSymbol(symbol) : symbol
      )
    );
    const calls = ids.map(calleeOf);
    const [declarations, called] = await Promise.all([
      Promise.all(targets.map((symbol) => this.resolveDeclarations(symbol?.declarations ?? []))),
      this.calledDeclarations(calls),
    ]);
    ids.forEach((id, i) => {
      const nodes = declarations[i] ?? [];
      const signature = called[i];
      this.definitions.set(id, signature ? withCalledDeclaration(nodes, signature) : nodes);
    });
  }

  /**
   * For each call (or `new`), the declaration of the signature the checker
   * resolved it to, when that is a function-like node (TS goToDefinition's
   * `tryGetSignatureDeclaration`; a function *type* does not count).
   */
  private async calledDeclarations(
    calls: readonly (CallExpression | NewExpression | undefined)[]
  ): Promise<(Declaration | undefined)[]> {
    const signatures = await Promise.all(
      calls.map((call) => (call ? this.checker.getResolvedSignature(call) : undefined))
    );
    const nodes = await this.resolveEach(signatures.map((signature) => signature?.declaration));
    return nodes.map((node) => (node && isSignatureDeclarationLike(node) ? node : undefined));
  }

  /**
   * ts-morph `identifier.getDefinitionNodes()`, after `prefetchDefinitions`.
   * Throws for an identifier that was not prefetched: an empty answer would
   * be indistinguishable from "no definition".
   */
  definitionNodes(id: Node): readonly Declaration[] {
    const nodes = this.definitions.get(id);
    if (!nodes) {
      throw new Error(
        `definitionNodes: identifier at ${id.getSourceFile().fileName}:${id.pos} was not prefetched; pass it to prefetchDefinitions()`
      );
    }
    return nodes;
  }

  /**
   * Resolve the module of every import declaration in `sourceFiles`, once,
   * so `moduleSpecifierSourceFile` can answer synchronously.
   */
  prefetchImports(): Promise<void> {
    if (!this.imports) this.imports = this.resolveImports();
    return this.imports;
  }

  private async resolveImports(): Promise<void> {
    const decls = this.sourceFiles.flatMap(importDeclarations);
    const symbols = await this.checker.getSymbolAtLocation(
      decls.map((decl) => decl.moduleSpecifier)
    );
    // ts-morph: the module symbol's first declaration, if it is a SourceFile.
    // An ambient `declare module "x"` (e.g. `bun` in @types/bun) is unresolved.
    const paths = symbols.map((symbol) => {
      const first = symbol?.declarations[0];
      return first && first.kind === SyntaxKind.SourceFile ? first.path : undefined;
    });
    const files = await Promise.all(
      paths.map((path) => (path ? this.fileAtPath(path) : undefined))
    );
    decls.forEach((decl, i) => {
      this.importTargets.set(decl, files[i]);
    });
  }

  /**
   * ts-morph `importDecl.getModuleSpecifierSourceFile()`, after
   * `prefetchImports`. A target outside `sourceFiles` (a node_modules
   * declaration file) is returned as ts-morph returns it. Throws for an
   * import declaration that was not prefetched.
   */
  moduleSpecifierSourceFile(importDecl: ImportDeclaration): SourceFile | undefined {
    if (!this.importTargets.has(importDecl)) {
      throw new Error(
        `moduleSpecifierSourceFile: import in ${importDecl.getSourceFile().fileName} was not prefetched; call prefetchImports()`
      );
    }
    return this.importTargets.get(importDecl);
  }
}

/** TS 6's creation order of the `typeof` result literals (checker typeofNEFacts). */
const TYPEOF_ORDER = [
  "string",
  "number",
  "bigint",
  "boolean",
  "symbol",
  "undefined",
  "object",
  "function",
];

function typeofRank(type: Type): number | undefined {
  if (!type.isStringLiteralType()) return undefined;
  const rank = TYPEOF_ORDER.indexOf(type.value);
  return rank === -1 ? undefined : rank;
}

/** The call or `new` expression whose callee `id` is. */
function calleeOf(id: Identifier): CallExpression | NewExpression | undefined {
  const parent = id.parent;
  if ((isCallExpression(parent) || isNewExpression(parent)) && parent.expression === id)
    return parent;
  return undefined;
}

/** TS `isFunctionLike(d) && !isFunctionTypeNode(d)`, over the node kinds a resolved signature can name. */
function isSignatureDeclarationLike(node: Declaration): boolean {
  return (
    isFunctionDeclaration(node) ||
    isFunctionExpression(node) ||
    isArrowFunction(node) ||
    isMethodDeclaration(node) ||
    isMethodSignatureDeclaration(node) ||
    isConstructorDeclaration(node) ||
    isGetAccessorDeclaration(node) ||
    isSetAccessorDeclaration(node) ||
    isCallSignatureDeclaration(node) ||
    isConstructSignatureDeclaration(node)
  );
}

/**
 * The node ts-morph maps a signature definition to: the parent of the
 * identifier at the definition's span. A named declaration is itself; an
 * unnamed function takes the name it is assigned to (`const f = () => …`),
 * and an unnamed, unassigned one has no definition node.
 */
function signatureDefinitionNode(declaration: Declaration): Declaration | undefined {
  if (!isArrowFunction(declaration) && !(isFunctionExpression(declaration) && !declaration.name)) {
    return declaration;
  }
  const parent = declaration.parent;
  if (
    isVariableDeclaration(parent) ||
    isPropertyAssignment(parent) ||
    isPropertyDeclaration(parent)
  )
    return parent;
  return undefined;
}

function sameNode(a: Node, b: Node): boolean {
  return (
    a === b ||
    (a.kind === b.kind &&
      a.pos === b.pos &&
      a.end === b.end &&
      a.getSourceFile().fileName === b.getSourceFile().fileName)
  );
}

/**
 * TS goToDefinition: when the symbol is the called declaration's own symbol
 * the called declaration alone, else the symbol's declarations plus it.
 * "Own symbol" is approximated as: the called declaration (or the variable
 * holding it) is one of the declarations, all in its file. A global merged
 * across files (`setTimeout` in @types/node and bun-types) gets a merged
 * symbol, so there TS lists every declaration, and so does this.
 */
function withCalledDeclaration(declarations: Declaration[], called: Declaration): Declaration[] {
  const node = signatureDefinitionNode(called);
  const file = called.getSourceFile().fileName;
  const own =
    declarations.some((d) => sameNode(d, called) || (node !== undefined && sameNode(d, node))) &&
    declarations.every((d) => d.getSourceFile().fileName === file);
  if (own) return node ? [node] : [];
  if (!node || declarations.some((d) => sameNode(d, node))) return declarations;
  return [...declarations, node];
}

// ---------------------------------------------------------------- session

/** One tsgo process for a CLI run. MUST be closed: an open API keeps the process alive forever. */
export class AnalysisSession implements AsyncDisposable {
  private readonly cwd: string;
  private api: API | undefined;
  private readonly snapshots: Promise<Snapshot>[] = [];
  private readonly programs = new Map<string, Promise<AnalysisProgram>>();
  private closed = false;

  constructor(options: { cwd?: string } = {}) {
    this.cwd = options.cwd ?? process.cwd();
  }

  /** Cached per resolved tsconfig path: every extractor on one tsconfig shares one program. */
  open(tsconfig: string): Promise<AnalysisProgram> {
    if (this.closed) return Promise.reject(new Error("AnalysisSession is closed"));
    const key = resolve(this.cwd, tsconfig);
    let program = this.programs.get(key);
    if (!program) {
      program = this.load(key);
      this.programs.set(key, program);
    }
    return program;
  }

  /**
   * A program on its own snapshot, so its checker starts fresh: types it is
   * asked about are created (and numbered) as if nothing had run before, as
   * with ts-morph's one Project per extractor. Use it where output follows
   * union-member order (types.ts); everything else shares `open`. Not cached.
   */
  openIsolated(tsconfig: string): Promise<AnalysisProgram> {
    if (this.closed) return Promise.reject(new Error("AnalysisSession is closed"));
    return this.load(resolve(this.cwd, tsconfig));
  }

  private async load(tsconfig: string): Promise<AnalysisProgram> {
    if (!existsSync(tsconfig)) throw new Error(`File not found: ${tsconfig}`);
    this.api ??= new API({ cwd: this.cwd });
    const pending = this.api.createSnapshot({ openProjects: [tsconfig], ensurePrograms: true });
    this.snapshots.push(pending);
    const snapshot = await pending;
    const project = snapshot.getConfiguredProject(tsconfig);
    if (!project) throw new Error(`typescript-7 could not open the project for ${tsconfig}`);
    return AnalysisProgram.load(tsconfig, project);
  }

  /** Stops the tsgo process. Idempotent; programs from this session are unusable afterwards. */
  async close(): Promise<void> {
    if (this.closed) return;
    this.closed = true;
    const api = this.api;
    this.api = undefined;
    if (!api) return;
    await Promise.allSettled(this.snapshots);
    await api.close();
  }

  async [Symbol.asyncDispose](): Promise<void> {
    await this.close();
  }
}

/** Run `fn` with a fresh session and always close it, however `fn` ends. */
export async function withAnalysisSession<T>(
  fn: (session: AnalysisSession) => Promise<T>,
  options: { cwd?: string } = {}
): Promise<T> {
  const session = new AnalysisSession(options);
  try {
    return await fn(session);
  } finally {
    await session.close();
  }
}

/** Where an extractor gets its program: a session (it opens its tsconfig there) or an open program. */
export type AnalysisSource = AnalysisSession | AnalysisProgram;

/**
 * Run `fn` on the program for `tsconfig`: the given program as is, the
 * project opened in the given session, or a session of its own, closed
 * however `fn` ends. A caller that passes a source keeps ownership of it.
 */
export async function withProgram<T>(
  tsconfig: string,
  source: AnalysisSource | undefined,
  fn: (program: AnalysisProgram) => T | Promise<T>
): Promise<T> {
  if (source instanceof AnalysisProgram) return fn(source);
  if (source instanceof AnalysisSession) return fn(await source.open(tsconfig));
  return withAnalysisSession(async (session) => fn(await session.open(tsconfig)));
}
