// Every synchronous AST helper, checked node by node against the answers
// ts-morph 28 gave for the method it replaces (recorded in oracle/ast.json),
// on frozen copies of real projects (full-featured, the types corpus) and on
// an edge-case project written to a temp dir.

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import * as path from "node:path";
import type { Node, SourceFile } from "typescript-7/ast";
import {
  isArrowFunction,
  isCallExpression,
  isFunctionDeclaration,
  isFunctionExpression,
  isImportSpecifier,
  isMethodDeclaration,
  isObjectLiteralExpression,
  isPropertyAssignment,
  isShorthandPropertyAssignment,
  isTypeAliasDeclaration,
  isVariableDeclaration,
  isVariableDeclarationList,
} from "typescript-7/ast/is";
import { AnalysisSession } from "../analysis-program";
import {
  declarationKind,
  firstAncestor,
  firstDescendant,
  forEachDescendant,
  functionDeclaration,
  functionDeclarations,
  hasExportKeyword,
  importDeclarations,
  importedName,
  jsDocDescription,
  jsDocs,
  jsDocText,
  kindName,
  leadingComments,
  lineAndColumn,
  literalValue,
  moduleSpecifierValue,
  namedImports,
  nameOf,
  objectProperty,
  startLine,
  startLinePos,
  startOf,
  textOf,
  typeAlias,
  typeAliases,
  variableDeclaration,
  variableStatements,
} from "../ast";
import {
  type Corpora,
  type CorpusName,
  Mismatches,
  readOracle,
  sha256,
  writeCorpora,
} from "./corpus";

/** Node kinds TS 7 reshaped (MAPPING.md §5.7); the extractors never read either side of a pair. */
const KNOWN_KIND_PAIRS = new Set([
  "ExpressionWithTypeArguments>TypeReference",
  "OmittedExpression>BindingElement",
]);

/** ts-morph's answers for one node, beyond the fixed row; absent means undefined (or [] for `d`). */
interface NodeExtra {
  /** getLiteralValue() */
  l?: string | number;
  /** getName() */
  n?: string;
  /** getJsDocs() as [getDescription(), getText()] */
  d?: [string, string][];
  /** getDeclarationKind() on a VariableDeclarationList */
  k?: string;
  /** ObjectLiteralExpression: getProperty(name)?.getStart() for each property name and "missing" */
  o?: [string, number | null][];
  /** CallExpression: getStart() of the first enclosing function-like */
  a?: number | null;
  /** FunctionDeclaration / ArrowFunction: getStart() of the first CallExpression inside */
  f?: number | null;
}

interface Statements {
  typeAliases: [string, number][];
  functions: [string | undefined, number, boolean][];
  functionLookups: [string, number | null][];
  variableStatements: [number, boolean][];
  variableLookups: [string, number | null][];
  imports: [string, string[]][];
  leadingComments: string[][];
}

interface OracleFile {
  corpus: CorpusName;
  path: string;
  sha: string;
  /** Per node in forEachDescendant order: [kind, getStart, getText length, getStartLineNumber, getStartLinePos, line, column]. */
  nodes: [number, number, number, number, number, number, number][];
  extra: Record<string, NodeExtra>;
  statements: Statements;
}

interface AstOracle {
  kinds: string[];
  files: OracleFile[];
  forEachStop: { hit: string; visited: number };
  documented: string[];
}

interface FilePair {
  where: string;
  expected: OracleFile;
  ts7: SourceFile;
}

const oracle = readOracle<AstOracle>("ast.json");
const session = new AnalysisSession();
const pairs: FilePair[] = [];
let corpora: Corpora | undefined;

beforeAll(async () => {
  const written = writeCorpora();
  corpora = written;
  for (const name of ["edge", "types-corpus", "full-featured"] as const) {
    const program = await session.open(written.tsconfig(name));
    for (const expected of oracle.files.filter((f) => f.corpus === name)) {
      const file = expected.path.startsWith("<edge>/")
        ? path.join(written.edge.root, expected.path.slice("<edge>/".length))
        : path.join(written.tree, expected.path);
      const ts7 = program.sourceFile(file);
      if (!ts7) throw new Error(`${name}: TS 7 program has no ${file}`);
      pairs.push({ where: `${name}:${expected.path}`, expected, ts7 });
    }
  }
}, 60_000);

afterAll(async () => {
  await session.close();
  corpora?.remove();
});

function ts7Descendants(root: Node): Node[] {
  const out: Node[] = [];
  forEachDescendant(root, (node) => {
    out.push(node);
  });
  return out;
}

/** One recorded node: its row, kind name and extras. */
interface Expected {
  index: number;
  kind: string;
  start: number;
  textLength: number;
  startLine: number;
  startLinePos: number;
  line: number;
  column: number;
  extra: NodeExtra;
}

/** The recorded walk and the TS 7 walk of one file, zipped; an error row when their lengths differ. */
function zipped(pair: FilePair, out: Mismatches): [Expected, Node][] {
  const b = ts7Descendants(pair.ts7);
  out.check(pair.where, "node count", pair.expected.nodes.length, b.length);
  return pair.expected.nodes.flatMap((row, index): [Expected, Node][] => {
    const n = b[index];
    const [kind, start, textLength, line0, linePos, line, column] = row;
    const e: Expected = {
      index,
      kind: oracle.kinds[kind] ?? `?${kind}`,
      start,
      textLength,
      startLine: line0,
      startLinePos: linePos,
      line,
      column,
      extra: pair.expected.extra[String(index)] ?? {},
    };
    return n ? [[e, n]] : [];
  });
}

function ts7Name(node: Node): string | undefined {
  if (isImportSpecifier(node)) return importedName(node);
  if (
    isFunctionDeclaration(node) ||
    isVariableDeclaration(node) ||
    isPropertyAssignment(node) ||
    isShorthandPropertyAssignment(node) ||
    isMethodDeclaration(node) ||
    isTypeAliasDeclaration(node)
  ) {
    return nameOf(node);
  }
  return undefined;
}

const orUndefined = <T>(value: T | null | undefined): T | undefined => value ?? undefined;

/** Returns true when the kinds differ in a known, harmless way. */
function compareKind(e: Expected, n: Node, at: string, out: Mismatches): boolean {
  if (e.kind === kindName(n)) return false;
  if (KNOWN_KIND_PAIRS.has(`${e.kind}>${kindName(n)}`)) return true;
  out.check(at, "kind", e.kind, kindName(n));
  return false;
}

function comparePositions(e: Expected, n: Node, sf: SourceFile, at: string, out: Mismatches): void {
  // The recorded text is a slice of the file the hash pins (record.ts checks it).
  out.check(at, "text", sf.text.slice(e.start, e.start + e.textLength), textOf(n, sf));
  out.check(at, "start", e.start, startOf(n, sf));
  out.check(at, "startLine", e.startLine, startLine(n, sf));
  out.check(at, "startLinePos", e.startLinePos, startLinePos(n, sf));
  out.check(
    at,
    "lineAndColumn",
    { line: e.line, column: e.column },
    lineAndColumn(sf, n.getStart(sf))
  );
}

function compareContent(e: Expected, n: Node, sf: SourceFile, at: string, out: Mismatches): void {
  out.check(at, "literal", e.extra.l, literalValue(n));
  out.check(at, "name", e.extra.n, ts7Name(n));
  out.check(
    at,
    "jsDocs",
    e.extra.d ?? [],
    jsDocs(n).map((d) => [jsDocDescription(d, sf), jsDocText(d, sf)])
  );
  if (e.extra.k !== undefined || isVariableDeclarationList(n)) {
    out.check(
      at,
      "declarationKind",
      e.extra.k,
      isVariableDeclarationList(n) ? declarationKind(n) : undefined
    );
  }
}

const isFunctionLike = (node: Node): node is Node =>
  isFunctionDeclaration(node) || isArrowFunction(node) || isFunctionExpression(node);

function compareLookups(e: Expected, n: Node, sf: SourceFile, at: string, out: Mismatches): void {
  const { o, a, f } = e.extra;
  if (o) {
    for (const [name, start] of o) {
      out.check(
        at,
        `objectProperty(${name})`,
        orUndefined(start),
        isObjectLiteralExpression(n) ? objectProperty(n, name)?.getStart(sf) : "not an object"
      );
    }
  }
  if (a !== undefined) {
    out.check(
      at,
      "firstAncestor",
      orUndefined(a),
      isCallExpression(n) ? firstAncestor(n, isFunctionLike)?.getStart(sf) : "not a call"
    );
  }
  if (f !== undefined) {
    out.check(
      at,
      "firstDescendant",
      orUndefined(f),
      firstDescendant(n, isCallExpression)?.getStart(sf)
    );
  }
}

function compareStatements(pair: FilePair, out: Mismatches): void {
  const { where, ts7 } = pair;
  const e = pair.expected.statements;
  out.check(where, "sha", pair.expected.sha, sha256(ts7.text));
  out.check(
    where,
    "typeAliases",
    e.typeAliases.map(([name]) => name),
    typeAliases(ts7).map(nameOf)
  );
  for (const [name, start] of e.typeAliases) {
    out.check(where, `typeAlias(${name})`, start, typeAlias(ts7, name)?.getStart(ts7));
  }
  out.check(
    where,
    "functions",
    e.functions,
    functionDeclarations(ts7).map((f) => [nameOf(f), f.getStart(ts7), hasExportKeyword(f)])
  );
  for (const [name, start] of e.functionLookups) {
    out.check(
      where,
      `function(${name})`,
      orUndefined(start),
      functionDeclaration(ts7, name)?.getStart(ts7)
    );
  }
  out.check(
    where,
    "variableStatements",
    e.variableStatements,
    variableStatements(ts7).map((s) => [s.getStart(ts7), hasExportKeyword(s)])
  );
  for (const [name, start] of e.variableLookups) {
    out.check(
      where,
      `variableDeclaration(${name})`,
      orUndefined(start),
      variableDeclaration(ts7, name)?.getStart(ts7)
    );
  }
  out.check(
    where,
    "imports",
    e.imports,
    importDeclarations(ts7).map((d) => [moduleSpecifierValue(d), namedImports(d).map(importedName)])
  );
  out.check(
    where,
    "leadingComments",
    e.leadingComments,
    ts7.statements.map((s) => leadingComments(s, ts7).map((r) => r.text))
  );
}

function edgePair(): FilePair {
  const pair = pairs.find((p) => p.where === "edge:<edge>/src/edge.ts");
  if (!pair) throw new Error("edge.ts missing");
  return pair;
}

describe("ast helpers match the recorded ts-morph answers node by node", () => {
  test("walk order, kind, text, positions, lines, literals, names, JSDoc, declaration kind", () => {
    const out = new Mismatches();
    let compared = 0;
    let knownKindDiffs = 0;
    for (const pair of pairs) {
      for (const [e, n] of zipped(pair, out)) {
        compared++;
        const at = `${pair.where}@${e.start} ${e.kind}`;
        if (compareKind(e, n, at, out)) knownKindDiffs++;
        comparePositions(e, n, pair.ts7, at, out);
        compareContent(e, n, pair.ts7, at, out);
      }
    }
    expect(out.head()).toEqual([]);
    expect(compared).toBeGreaterThan(30_000);
    // Heritage clauses: `implements X<T>` is a TypeReference in TS 7.
    expect(knownKindDiffs).toBeLessThan(50);
  });

  test("statement accessors: type aliases, functions, variables, imports, comments, export keyword", () => {
    const out = new Mismatches();
    for (const pair of pairs) compareStatements(pair, out);
    expect(out.head()).toEqual([]);
  });

  test("objectProperty, firstAncestor and firstDescendant", () => {
    const out = new Mismatches();
    let objects = 0;
    for (const pair of pairs) {
      for (const [e, n] of zipped(pair, out)) {
        if (e.kind === "ObjectLiteralExpression") objects++;
        compareLookups(e, n, pair.ts7, `${pair.where}@${e.start}`, out);
      }
    }
    expect(out.head()).toEqual([]);
    expect(objects).toBeGreaterThan(50);
  });

  test("forEachDescendant stops on a truthy callback value, as ts-morph does", () => {
    const pair = edgePair();
    let visited = 0;
    const hit = forEachDescendant(pair.ts7, (node) => {
      visited++;
      return isCallExpression(node) ? textOf(node, pair.ts7) : undefined;
    });
    expect(hit).toBe(oracle.forEachStop.hit);
    expect(visited).toBe(oracle.forEachStop.visited);
    expect(visited).toBeLessThan(ts7Descendants(pair.ts7).length);
  });

  test("the edge project exercises what it claims to", () => {
    const { ts7 } = edgePair();
    expect(ts7.text.includes("\r/")).toBe(true);
    expect(ts7.text.includes("\u2028")).toBe(true);
    // TS 7's own line map breaks on the CR and the U+2028; ts-morph (and startLine) do not.
    const last = ts7.statements.at(-1);
    if (!last) throw new Error("no statements");
    const ts7Line = ts7.getLineAndCharacterOfPosition(last.getStart(ts7)).line + 1;
    expect(startLine(last, ts7)).toBe(ts7Line - 2);
    const description = jsDocs(functionDeclaration(ts7, "documented")).map((d) =>
      jsDocDescription(d, ts7)
    );
    expect(description).toEqual(oracle.documented);
    expect(description[0]).toContain("description\nsecond line");
  });
});
