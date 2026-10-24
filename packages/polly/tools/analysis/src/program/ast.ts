// Synchronous AST helpers over typescript-7 nodes, each reproducing the
// ts-morph method the extractors call today (named in the doc comment).
//
// A fetched typescript-7 SourceFile is a plain local tree: everything here is
// free of IPC. Positions and line numbers follow ts-morph's text-based rules
// (it counts `\n` only; TS 7's line map also breaks on `\r`, U+2028 and
// U+2029), so a file with a lone CR or a line separator in a string keeps the
// line numbers ts-morph gave it.

import type {
  FunctionDeclaration,
  ImportDeclaration,
  ImportSpecifier,
  JSDoc,
  Node,
  NoSubstitutionTemplateLiteral,
  NumericLiteral,
  ObjectLiteralElementLike,
  ObjectLiteralExpression,
  SourceFile,
  StringLiteral,
  TypeAliasDeclaration,
  VariableDeclaration,
  VariableDeclarationList,
  VariableStatement,
} from "typescript-7/ast";
import { formatSyntaxKind, getLeadingCommentRanges, NodeFlags, SyntaxKind } from "typescript-7/ast";
import {
  isArrayBindingPattern,
  isBindingElement,
  isFunctionDeclaration,
  isImportDeclaration,
  isJSDoc,
  isNamedImports,
  isNoSubstitutionTemplateLiteral,
  isNumericLiteral,
  isObjectBindingPattern,
  isStringLiteral,
  isTypeAliasDeclaration,
  isVariableStatement,
} from "typescript-7/ast/is";

// ---------------------------------------------------------------- text and positions

/** ts-morph `node.getText()`: from getStart (leading trivia excluded) to end. */
export function textOf(node: Node, sourceFile: SourceFile = node.getSourceFile()): string {
  return node.getText(sourceFile);
}

/** ts-morph `node.getStart()`. */
export function startOf(node: Node, sourceFile: SourceFile = node.getSourceFile()): number {
  return node.getStart(sourceFile);
}

const newlineOffsets = new WeakMap<SourceFile, number[]>();

/** Offsets of every `\n` in the file's text, cached per file. */
function newlinesOf(sourceFile: SourceFile): number[] {
  let offsets = newlineOffsets.get(sourceFile);
  if (!offsets) {
    offsets = [];
    const text = sourceFile.text;
    for (let i = text.indexOf("\n"); i !== -1; i = text.indexOf("\n", i + 1)) offsets.push(i);
    newlineOffsets.set(sourceFile, offsets);
  }
  return offsets;
}

/** ts-morph `StringUtils.getLineNumberAtPos`: 1 + the number of `\n` before `pos`. */
function lineNumberAt(sourceFile: SourceFile, pos: number): number {
  const offsets = newlinesOf(sourceFile);
  let lo = 0;
  let hi = offsets.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    const offset = offsets[mid];
    if (offset !== undefined && offset < pos) lo = mid + 1;
    else hi = mid;
  }
  return lo + 1;
}

/** ts-morph `StringUtils.getLineStartFromPos`: back up to just after the previous `\n` or `\r`. */
function lineStartAt(text: string, pos: number): number {
  let start = pos;
  while (start > 0) {
    const previous = text.charCodeAt(start - 1);
    if (previous === 10 || previous === 13) break;
    start--;
  }
  return start;
}

/** ts-morph `node.getStartLineNumber()`: 1-based line of getStart. */
export function startLine(node: Node, sourceFile: SourceFile = node.getSourceFile()): number {
  return lineNumberAt(sourceFile, node.getStart(sourceFile));
}

/** ts-morph `node.getStartLinePos()`: offset of the start of getStart's line. */
export function startLinePos(node: Node, sourceFile: SourceFile = node.getSourceFile()): number {
  return lineStartAt(sourceFile.text, node.getStart(sourceFile));
}

/** ts-morph `sourceFile.getLineAndColumnAtPos(pos)`: both 1-based. */
export function lineAndColumn(
  sourceFile: SourceFile,
  pos: number
): { line: number; column: number } {
  return {
    line: lineNumberAt(sourceFile, pos),
    column: pos - lineStartAt(sourceFile.text, pos) + 1,
  };
}

/** ts-morph `node.getKindName()`. SyntaxKind numbers differ between TS 6 and 7; names are stable. */
export function kindName(node: Node): string {
  return formatSyntaxKind(node.kind);
}

/**
 * ts-morph `node.getName()` on a named declaration or property: the name
 * node's text (quotes kept for a string-literal name, as ts-morph keeps them).
 * For an ImportSpecifier use `importedName`: ts-morph names it by `propertyName`.
 */
export function nameOf(node: Node & { readonly name?: Node | undefined }): string | undefined {
  return node.name?.getText(node.getSourceFile());
}

// ---------------------------------------------------------------- literals

/** ts-morph `getLiteralValue()` on a StringLiteral, NoSubstitutionTemplateLiteral or NumericLiteral. */
export function literalValue(node: StringLiteral | NoSubstitutionTemplateLiteral): string;
export function literalValue(node: NumericLiteral): number;
export function literalValue(node: Node): string | number | undefined;
export function literalValue(node: Node): string | number | undefined {
  if (isStringLiteral(node) || isNoSubstitutionTemplateLiteral(node)) return node.text;
  if (isNumericLiteral(node)) {
    return node.text.includes(".") ? Number.parseFloat(node.text) : Number.parseInt(node.text, 10);
  }
  return undefined;
}

// ---------------------------------------------------------------- traversal

/**
 * ts-morph `node.forEachDescendant(cb)`: every descendant (not `root`
 * itself), depth first in `forEachChild` order. As in ts-morph, a truthy
 * return value from `cb` stops the whole walk and is returned.
 */
export function forEachDescendant<T>(root: Node, cb: (node: Node) => T | undefined): T | undefined {
  let result: T | undefined;
  const visit = (node: Node): boolean | undefined => {
    const value = cb(node);
    if (value) {
      result = value;
      return true;
    }
    return node.forEachChild(visit);
  };
  root.forEachChild(visit);
  return result;
}

/** ts-morph `getFirstDescendantByKind(kind)` / `getFirstDescendant(pred)`: first match in walk order. */
export function firstDescendant<T extends Node>(
  root: Node,
  pred: (node: Node) => node is T
): T | undefined {
  return forEachDescendant(root, (node) => (pred(node) ? node : undefined));
}

/** ts-morph `getFirstAncestorByKind(kind)` / `getFirstAncestor(pred)`: nearest match above `node`. */
export function firstAncestor<T extends Node>(
  node: Node,
  pred: (node: Node) => node is T
): T | undefined {
  for (let parent: Node | undefined = node.parent; parent; parent = parent.parent) {
    if (pred(parent)) return parent;
  }
  return undefined;
}

// ---------------------------------------------------------------- statements of a file

/** ts-morph `sourceFile.getTypeAliases()`: top-level type aliases. */
export function typeAliases(sourceFile: SourceFile): TypeAliasDeclaration[] {
  return sourceFile.statements.filter(isTypeAliasDeclaration);
}

/** ts-morph `sourceFile.getTypeAlias(name)`. */
export function typeAlias(sourceFile: SourceFile, name: string): TypeAliasDeclaration | undefined {
  return typeAliases(sourceFile).find((alias) => nameOf(alias) === name);
}

/** ts-morph `sourceFile.getFunctions()`: implementations and ambient declarations, not overload signatures. */
export function functionDeclarations(sourceFile: SourceFile): FunctionDeclaration[] {
  return sourceFile.statements
    .filter(isFunctionDeclaration)
    .filter((fn) => fn.body !== undefined || isAmbient(fn));
}

/** ts-morph `sourceFile.getFunction(name)`. */
export function functionDeclaration(
  sourceFile: SourceFile,
  name: string
): FunctionDeclaration | undefined {
  return functionDeclarations(sourceFile).find((fn) => nameOf(fn) === name);
}

/** ts-morph `sourceFile.getVariableStatements()`. */
export function variableStatements(sourceFile: SourceFile): VariableStatement[] {
  return sourceFile.statements.filter(isVariableStatement);
}

/** ts-morph `sourceFile.getVariableDeclaration(name)`: a top-level declaration, binding patterns searched. */
export function variableDeclaration(
  sourceFile: SourceFile,
  name: string
): VariableDeclaration | undefined {
  for (const statement of variableStatements(sourceFile)) {
    for (const declaration of statement.declarationList.declarations) {
      if (bindsName(declaration.name, name)) return declaration;
    }
  }
  return undefined;
}

function bindsName(binding: Node, name: string): boolean {
  if (isObjectBindingPattern(binding) || isArrayBindingPattern(binding)) {
    return binding.elements.some(
      (element) =>
        isBindingElement(element) && element.name !== undefined && bindsName(element.name, name)
    );
  }
  return binding.getText(binding.getSourceFile()) === name;
}

/** ts-morph `sourceFile.getImportDeclarations()`. */
export function importDeclarations(sourceFile: SourceFile): ImportDeclaration[] {
  return sourceFile.statements.filter(isImportDeclaration);
}

/** ts-morph `importDecl.getModuleSpecifierValue()`. */
export function moduleSpecifierValue(importDecl: ImportDeclaration): string | undefined {
  const specifier = importDecl.moduleSpecifier;
  return isStringLiteral(specifier) ? specifier.text : undefined;
}

/** ts-morph `importDecl.getNamedImports()`. */
export function namedImports(importDecl: ImportDeclaration): readonly ImportSpecifier[] {
  const bindings = importDecl.importClause?.namedBindings;
  return bindings && isNamedImports(bindings) ? bindings.elements : [];
}

/** ts-morph `importSpecifier.getName()`: the imported name (`a` in `{ a as b }`), not the local alias. */
export function importedName(specifier: ImportSpecifier): string {
  const node = specifier.propertyName ?? specifier.name;
  return node.getText(specifier.getSourceFile());
}

/** ts-morph `objectLiteral.getProperty(name)`: first property whose name text is `name`. */
export function objectProperty(
  objectLiteral: ObjectLiteralExpression,
  name: string
): ObjectLiteralElementLike | undefined {
  return objectLiteral.properties.find(
    (property) => "name" in property && nameOf(property) === name
  );
}

/** ts-morph `variableDeclarationList.getDeclarationKind()`. */
export function declarationKind(
  list: VariableDeclarationList
): "var" | "let" | "const" | "using" | "await using" {
  const flags = list.flags;
  if (flags & NodeFlags.Let) return "let";
  if ((flags & NodeFlags.AwaitUsing) === NodeFlags.AwaitUsing) return "await using";
  if ((flags & NodeFlags.Using) === NodeFlags.Using) return "using";
  if (flags & NodeFlags.Const) return "const";
  return "var";
}

// ---------------------------------------------------------------- modifiers

/** ts-morph `hasExportKeyword()`: an `export` modifier on the node itself. */
export function hasExportKeyword(node: FunctionDeclaration | VariableStatement): boolean {
  return node.modifiers?.some((modifier) => modifier.kind === SyntaxKind.ExportKeyword) ?? false;
}

/**
 * ts-morph `isAmbient()` for a top-level function: a `declare` modifier or a
 * declaration file (its only ancestor, the SourceFile, is never ambient).
 */
function isAmbient(fn: FunctionDeclaration): boolean {
  return (
    fn.getSourceFile().isDeclarationFile ||
    (fn.modifiers?.some((modifier) => modifier.kind === SyntaxKind.DeclareKeyword) ?? false)
  );
}

// ---------------------------------------------------------------- comments

/** ts-morph `Node.isJSDocable(node)`: the kinds ts-morph exposes `getJsDocs()` on. */
const JSDOCABLE_KINDS: ReadonlySet<SyntaxKind> = new Set([
  SyntaxKind.ArrowFunction,
  SyntaxKind.CallSignature,
  SyntaxKind.CaseClause,
  SyntaxKind.ClassDeclaration,
  SyntaxKind.ClassExpression,
  SyntaxKind.ClassStaticBlockDeclaration,
  SyntaxKind.Constructor,
  SyntaxKind.ConstructSignature,
  SyntaxKind.EnumDeclaration,
  SyntaxKind.EnumMember,
  SyntaxKind.ExportAssignment,
  SyntaxKind.ExpressionStatement,
  SyntaxKind.FunctionDeclaration,
  SyntaxKind.FunctionExpression,
  SyntaxKind.GetAccessor,
  SyntaxKind.ImportEqualsDeclaration,
  SyntaxKind.IndexSignature,
  SyntaxKind.InterfaceDeclaration,
  SyntaxKind.LabeledStatement,
  SyntaxKind.MethodDeclaration,
  SyntaxKind.MethodSignature,
  SyntaxKind.ModuleDeclaration,
  SyntaxKind.NamedTupleMember,
  SyntaxKind.PropertyDeclaration,
  SyntaxKind.PropertySignature,
  SyntaxKind.SetAccessor,
  SyntaxKind.TypeAliasDeclaration,
  SyntaxKind.VariableStatement,
]);

/** ts-morph `Node.isJSDocable(node)`. */
export function isJSDocable(node: Node | undefined): node is Node {
  return node !== undefined && JSDOCABLE_KINDS.has(node.kind);
}

/** ts-morph `Node.isJSDocable(node) ? node.getJsDocs() : []`. */
export function jsDocs(node: Node | undefined): readonly JSDoc[] {
  if (!isJSDocable(node)) return [];
  return (node.jsDoc ?? []).filter(isJSDoc);
}

const WHITESPACE = new Set(
  [" ", "\f", "\n", "\r", "\t", "\v", " ", " ", " "].map((c) => c.charCodeAt(0))
);

/**
 * Where a JSDoc comment's `/**` starts. TS 7 gives a JSDoc node the full
 * leading trivia (`pos`), and its getStart stops at the first comment, which
 * may be a `//` line above the `/**`; TS 6 started the node at the `/**`.
 */
function jsDocStart(doc: JSDoc, sourceFile: SourceFile): number {
  const own = (getLeadingCommentRanges(sourceFile.text, doc.pos) ?? []).find(
    (range) => range.end === doc.end
  );
  return own ? own.pos : doc.getStart(sourceFile);
}

/** ts-morph `jsDoc.getText()`: the comment from `/**` to `*\/`. */
export function jsDocText(doc: JSDoc, sourceFile: SourceFile = doc.getSourceFile()): string {
  return sourceFile.text.slice(jsDocStart(doc, sourceFile), doc.end);
}

/**
 * ts-morph `jsDoc.getDescription()`: the comment's text before its first tag,
 * stars stripped line by line, computed from the source text exactly as
 * ts-morph does (getTextOfJSDocComment normalises whitespace differently).
 */
export function jsDocDescription(doc: JSDoc, sourceFile: SourceFile = doc.getSourceFile()): string {
  const text = sourceFile.text;
  const firstTag = doc.tags?.[0];
  const endSearchStart = firstTag ? firstTag.getStart(sourceFile) : doc.end - 2;
  let start = jsDocStart(doc, sourceFile) + 3;
  if (text.charCodeAt(start) === 32) start++;
  const endOrNewLine = previousMatching(
    text,
    endSearchStart,
    (c) => c === 10 || (!WHITESPACE.has(c) && c !== 42)
  );
  const end = previousMatching(text, endOrNewLine, (c) => c !== 10 && c !== 13);
  return withoutStars(text.substring(start, Math.max(start, end)));
}

function previousMatching(
  text: string,
  pos: number,
  condition: (charCode: number) => boolean
): number {
  let current = pos;
  while (current > 0 && !condition(text.charCodeAt(current - 1))) current--;
  return current;
}

function withoutStars(input: string): string {
  const inner = input.replace(/^\/\*\*[^\S\n]*\n?/, "").replace(/(\r?\n)?[^\S\n]*\*\/$/, "");
  return inner
    .split(/\n/)
    .map((line) => {
      let star = -1;
      for (let i = 0; i < line.length; i++) {
        const c = line.charCodeAt(i);
        if (c === 42) {
          star = i;
          break;
        }
        if (!WHITESPACE.has(c)) break;
      }
      if (star === -1) return line;
      return line.substring(line[star + 1] === " " ? star + 2 : star + 1);
    })
    .join("\n");
}

/** ts-morph `statement.getLeadingCommentRanges()`: each comment's range and text. */
export function leadingComments(
  node: Node,
  sourceFile: SourceFile = node.getSourceFile()
): { pos: number; end: number; text: string }[] {
  if (node.kind === SyntaxKind.SourceFile) return [];
  return (getLeadingCommentRanges(sourceFile.text, node.pos) ?? []).map((range) => ({
    pos: range.pos,
    end: range.end,
    text: sourceFile.text.slice(range.pos, range.end),
  }));
}
