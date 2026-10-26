// Context analysis - analyze individual execution contexts

import type {
  ArrowFunction,
  ClassDeclaration,
  FunctionDeclaration,
  FunctionExpression,
  HeritageClauseElement,
  Node,
  SourceFile,
} from "typescript-7/ast";
import { SyntaxKind } from "typescript-7/ast";
import {
  isArrowFunction,
  isBlock,
  isClassDeclaration,
  isFunctionDeclaration,
  isFunctionExpression,
  isJsxElement,
  isJsxSelfClosingElement,
  isPropertyAccessExpression,
  isVariableDeclaration,
} from "typescript-7/ast/is";
import {
  type AnalysisProgram,
  type AnalysisSource,
  forEachDescendant,
  importDeclarations,
  jsDocDescription,
  jsDocs,
  leadingComments,
  moduleSpecifierValue,
  nameOf,
  startLine,
  textOf,
  withProgram,
} from "../program";
import type { ComponentInfo, ContextInfo } from "../types/architecture";
import type { MessageHandler } from "../types/core";

/** A component found in the walk, before its props are read from the checker. */
interface ComponentCandidate {
  info: Omit<ComponentInfo, "props">;
  props: () => Promise<string[]>;
}

export class ContextAnalyzer {
  private tsConfigPath: string;

  constructor(tsConfigPath: string) {
    this.tsConfigPath = tsConfigPath;
  }

  /**
   * Analyze a specific context given its entry point. With no `source`,
   * opens (and closes) a session of its own; a passed source stays the
   * caller's.
   */
  analyzeContext(
    contextType: string,
    entryPoint: string,
    handlers: MessageHandler[],
    source?: AnalysisSource
  ): Promise<ContextInfo> {
    return withProgram(this.tsConfigPath, source, (program) =>
      this.contextIn(program, contextType, entryPoint, handlers)
    );
  }

  private async contextIn(
    program: AnalysisProgram,
    contextType: string,
    entryPoint: string,
    handlers: MessageHandler[]
  ): Promise<ContextInfo> {
    const sourceFile = program.sourceFile(entryPoint);

    if (!sourceFile) {
      throw new Error(`Could not find source file: ${entryPoint}`);
    }

    // Extract Chrome API usage
    const chromeAPIs = this.extractChromeAPIs(sourceFile);

    // Extract dependencies
    const dependencies = this.extractDependencies(sourceFile);

    // Extract JSDoc description
    const description = this.extractDescription(sourceFile);

    // Extract components (for UI contexts)
    const components = this.isUIContext(contextType)
      ? await this.extractComponents(program, sourceFile)
      : undefined;

    // Filter handlers for this context
    const contextHandlers = handlers.filter((h) => h.node === contextType);

    return {
      type: contextType,
      entryPoint,
      handlers: contextHandlers,
      chromeAPIs,
      externalAPIs: [], // Will be filled by integration analyzer
      ...(components ? { components } : {}),
      dependencies,
      ...(description ? { description } : {}),
    };
  }

  /**
   * Extract Chrome API usage from source file
   */
  private extractChromeAPIs(sourceFile: SourceFile): string[] {
    const apis = new Set<string>();

    forEachDescendant(sourceFile, (node: Node) => {
      if (isPropertyAccessExpression(node)) {
        const text = textOf(node, sourceFile);
        this.detectAPIPattern(text, apis);
      }
    });

    return Array.from(apis).sort();
  }

  /**
   * Detect and extract API from text using various patterns
   */
  private detectAPIPattern(text: string, apis: Set<string>): void {
    // Match chrome.* API calls
    if (text.startsWith("chrome.")) {
      const api = this.extractAPIFromPrefix(text, "chrome");
      if (api) apis.add(api);
      return;
    }

    // Match browser.* for Firefox compatibility
    if (text.startsWith("browser.")) {
      const api = this.extractAPIFromPrefix(text, "browser");
      if (api) apis.add(api);
      return;
    }

    // Match bus.adapters.* pattern (framework abstraction)
    if (text.includes("bus.adapters.")) {
      const api = this.extractAPIFromBusAdapter(text);
      if (api) apis.add(api);
    }
  }

  /**
   * Extract API namespace from chrome.* or browser.* prefix
   */
  private extractAPIFromPrefix(text: string, prefix: string): string | null {
    // nosemgrep: javascript.lang.security.audit.detect-non-literal-regexp.detect-non-literal-regexp — prefix is a fixed identifier ("chrome" / "browser"), not user input.
    const pattern = new RegExp(`^${prefix}\\.([^.(]+(?:\\.[^.(]+)?)`);
    const match = text.match(pattern);
    return match?.[1] || null;
  }

  /**
   * Extract API from bus.adapters.* pattern
   */
  private extractAPIFromBusAdapter(text: string): string | null {
    const match = text.match(/bus\.adapters\.([^.(]+)/);
    return match?.[1] || null;
  }

  /**
   * Extract import dependencies
   */
  private extractDependencies(sourceFile: SourceFile): string[] {
    const deps: string[] = [];

    for (const importDecl of importDeclarations(sourceFile)) {
      const moduleSpecifier = moduleSpecifierValue(importDecl);
      if (moduleSpecifier !== undefined) deps.push(moduleSpecifier);
    }

    return deps;
  }

  /**
   * Extract JSDoc description from file
   */
  private extractDescription(sourceFile: SourceFile): string | undefined {
    // Look for file-level JSDoc comment
    const firstStatement = sourceFile.statements[0];
    if (!firstStatement) return undefined;

    return fileDescription(leadingComments(firstStatement, sourceFile).map((c) => c.text));
  }

  /**
   * Extract React/Preact components from source file. The walk is
   * synchronous; props are then read from the checker one component at a
   * time, in walk order, as ts-morph asked for them.
   */
  private async extractComponents(
    program: AnalysisProgram,
    sourceFile: SourceFile
  ): Promise<ComponentInfo[]> {
    const candidates: ComponentCandidate[] = [];

    forEachDescendant(sourceFile, (node: Node) => {
      this.extractFunctionComponent(program, node, sourceFile, candidates);
      this.extractArrowFunctionComponent(program, node, sourceFile, candidates);
      this.extractClassComponent(program, node, sourceFile, candidates);
    });

    const components: ComponentInfo[] = [];
    for (const candidate of candidates) {
      const { description, ...rest } = candidate.info;
      components.push({
        ...rest,
        props: await candidate.props(),
        ...(description ? { description } : {}),
      });
    }
    return components;
  }

  /**
   * Extract function component from node if applicable
   */
  private extractFunctionComponent(
    program: AnalysisProgram,
    node: Node,
    sourceFile: SourceFile,
    components: ComponentCandidate[]
  ): void {
    if (!isFunctionDeclaration(node)) return;

    const name = nameOf(node);
    if (!name || !this.looksLikeComponent(name, node)) return;

    const description = this.extractJSDocDescription(node);
    components.push({
      info: {
        name,
        type: "function",
        filePath: sourceFile.fileName,
        line: startLine(node, sourceFile),
        ...(description ? { description } : {}),
      },
      props: () => this.extractProps(program, node),
    });
  }

  /**
   * Extract arrow function component from node if applicable
   */
  private extractArrowFunctionComponent(
    program: AnalysisProgram,
    node: Node,
    sourceFile: SourceFile,
    components: ComponentCandidate[]
  ): void {
    if (!isVariableDeclaration(node)) return;

    const name = nameOf(node);
    const initializer = node.initializer;

    if (!name || !initializer) return;
    if (!isArrowFunction(initializer) && !isFunctionExpression(initializer)) return;
    if (!this.looksLikeComponent(name, initializer)) return;

    const description = this.extractJSDocDescription(node);
    components.push({
      info: {
        name,
        type: "function",
        filePath: sourceFile.fileName,
        line: startLine(node, sourceFile),
        ...(description ? { description } : {}),
      },
      props: () => this.extractProps(program, initializer),
    });
  }

  /**
   * Extract class component from node if applicable
   */
  private extractClassComponent(
    program: AnalysisProgram,
    node: Node,
    sourceFile: SourceFile,
    components: ComponentCandidate[]
  ): void {
    if (!isClassDeclaration(node)) return;

    const name = nameOf(node);
    if (!name || !this.looksLikeClassComponent(node)) return;

    const description = this.extractJSDocDescription(node);
    components.push({
      info: {
        name,
        type: "class",
        filePath: sourceFile.fileName,
        line: startLine(node, sourceFile),
        ...(description ? { description } : {}),
      },
      props: () => this.extractPropsFromClass(program, node),
    });
  }

  /**
   * Check if a function looks like a React/Preact component
   */
  private looksLikeComponent(
    name: string,
    node: FunctionDeclaration | ArrowFunction | FunctionExpression
  ): boolean {
    // Component names should start with uppercase
    if (!/^[A-Z]/.test(name)) return false;

    // Check if it returns JSX
    const body = node.body;
    if (!body) return false;

    let hasJSX = false;

    if (isBlock(body)) {
      forEachDescendant(body, (child: Node) => {
        if (isJsxElement(child) || isJsxSelfClosingElement(child)) {
          hasJSX = true;
        }
      });
    } else if (isJsxElement(body) || isJsxSelfClosingElement(body)) {
      // Arrow function with implicit return
      hasJSX = true;
    }

    return hasJSX;
  }

  /**
   * Check if a class looks like a React component
   */
  private looksLikeClassComponent(node: ClassDeclaration): boolean {
    const extendedTypes = classExtends(node);
    if (!extendedTypes) return false;

    const extendsText = textOf(extendedTypes);
    return /Component|PureComponent/.test(extendsText);
  }

  /**
   * Extract props from function component
   */
  private async extractProps(
    program: AnalysisProgram,
    node: FunctionDeclaration | ArrowFunction | FunctionExpression
  ): Promise<string[]> {
    const propsParam = node.parameters[0];
    if (!propsParam) return [];

    const type = await program.typeOf(propsParam);
    return program.propertyNames(type);
  }

  /**
   * Extract props from class component
   */
  private async extractPropsFromClass(
    program: AnalysisProgram,
    node: ClassDeclaration
  ): Promise<string[]> {
    const extendedTypes = classExtends(node);
    if (!extendedTypes) return [];

    const typeArgs = await program.typeArguments(await program.typeOf(extendedTypes));
    const propsType = typeArgs[0];
    if (!propsType) return [];

    return program.propertyNames(propsType);
  }

  /**
   * Extract JSDoc description from node
   */
  private extractJSDocDescription(node: Node): string | undefined {
    const firstDoc = jsDocs(node)[0];
    if (!firstDoc) return undefined;

    const description = jsDocDescription(firstDoc).trim();
    return description || undefined;
  }

  /**
   * Check if context is a UI context
   */
  private isUIContext(contextType: string): boolean {
    return ["popup", "options", "devtools"].includes(contextType);
  }
}

/** ts-morph `classDeclaration.getExtends()`: the first type of the `extends` clause. */
function classExtends(node: ClassDeclaration): HeritageClauseElement | undefined {
  const clause = node.heritageClauses?.find((c) => c.token === SyntaxKind.ExtendsKeyword);
  return clause?.types[0];
}

/** A `/// <reference … />` (or other triple-slash) directive: compiler input, not prose. */
const TRIPLE_SLASH_DIRECTIVE = /^\/\/\/\s*</;
/**
 * A line with no description in it: a JSDoc tag (`@module`, `@param x`), or
 * a title that is only a scoped package name (`@lingua/auth`), which the
 * container already shows. `@lingua/sync — cross-context …` is text.
 */
const NOT_DESCRIPTION = /^@\w+(?:\s|$)|^@[\w.-]+\/[\w.-]+$/;

/**
 * A file's description from the comments before its first statement: the
 * first comment that is not a triple-slash directive, read as its
 * `@description` tag, else its first text line that is not a JSDoc tag or
 * a bare package name.
 */
export function fileDescription(comments: readonly string[]): string | undefined {
  const comment = comments.find((c) => !TRIPLE_SLASH_DIRECTIVE.test(c));
  if (comment === undefined) return undefined;

  const descMatch = comment.match(/@description\s+(.+?)(?:\n|$)/s);
  if (descMatch?.[1]) {
    return descMatch[1].trim();
  }

  const lines = commentTextLines(comment).filter((l) => l && !NOT_DESCRIPTION.test(l));
  return lines[0] || undefined;
}

/**
 * The text lines of a comment, without its delimiters: `//`, the `/*` or
 * `/**` opener, the closing `*\/` and each line's leading `*`. A JSDoc opener
 * on a line of its own used to survive as the description `/**`.
 */
export function commentTextLines(comment: string): string[] {
  const body = comment.startsWith("//")
    ? comment.slice(2)
    : comment.replace(/^\/\*+/, "").replace(/\*+\/$/, "");
  return body.split("\n").map((line) => line.replace(/^[\s*]+/, "").trim());
}
