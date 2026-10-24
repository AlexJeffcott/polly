// Every synchronous AST helper, checked node by node against the ts-morph
// method it replaces, on real projects (full-featured, the types corpus) and
// on an edge-case project written to a temp dir.

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as path from "node:path";
import {
  Node as M,
  type Node as MorphNode,
  type SourceFile as MorphSourceFile,
  Project,
} from "ts-morph";
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
import { FULL_FEATURED, Mismatches, TYPES_CORPUS, writeEdgeProject } from "./corpus";

/** Node kinds TS 7 reshaped (MAPPING.md §5.7); the extractors never read either side of a pair. */
const KNOWN_KIND_PAIRS = new Set([
  "ExpressionWithTypeArguments>TypeReference",
  "OmittedExpression>BindingElement",
]);

interface FilePair {
  where: string;
  morph: MorphSourceFile;
  ts7: SourceFile;
}

const session = new AnalysisSession();
const pairs: FilePair[] = [];
let edgeRoot = "";

beforeAll(async () => {
  const edge = writeEdgeProject();
  edgeRoot = edge.root;
  const corpora = [
    ["edge", edge.tsconfig],
    ["types-corpus", TYPES_CORPUS],
    ["full-featured", FULL_FEATURED],
  ];
  for (const [name, tsconfig] of corpora) {
    if (!name || !tsconfig) continue;
    const morph = new Project({ tsConfigFilePath: tsconfig });
    const program = await session.open(tsconfig);
    for (const file of morph.getSourceFiles()) {
      const ts7 = program.sourceFile(file.getFilePath());
      if (!ts7) throw new Error(`${name}: TS 7 program has no ${file.getFilePath()}`);
      pairs.push({ where: `${name}:${path.basename(file.getFilePath())}`, morph: file, ts7 });
    }
  }
}, 60_000);

afterAll(async () => {
  await session.close();
  if (edgeRoot) fs.rmSync(edgeRoot, { recursive: true, force: true });
});

function morphDescendants(root: MorphNode): MorphNode[] {
  const out: MorphNode[] = [];
  root.forEachDescendant((node) => {
    out.push(node);
  });
  return out;
}

function ts7Descendants(root: Node): Node[] {
  const out: Node[] = [];
  forEachDescendant(root, (node) => {
    out.push(node);
  });
  return out;
}

/** The two walks of one file, zipped; an error row when their lengths differ. */
function zipped(pair: FilePair, out: Mismatches): [MorphNode, Node][] {
  const a = morphDescendants(pair.morph);
  const b = ts7Descendants(pair.ts7);
  out.check(pair.where, "node count", a.length, b.length);
  return a.flatMap((m, i): [MorphNode, Node][] => {
    const n = b[i];
    return n ? [[m, n]] : [];
  });
}

function morphName(node: MorphNode): string | undefined {
  if (
    M.isFunctionDeclaration(node) ||
    M.isVariableDeclaration(node) ||
    M.isPropertyAssignment(node) ||
    M.isShorthandPropertyAssignment(node) ||
    M.isMethodDeclaration(node) ||
    M.isTypeAliasDeclaration(node) ||
    M.isImportSpecifier(node)
  ) {
    return node.getName();
  }
  return undefined;
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

function morphLiteral(node: MorphNode): string | number | undefined {
  if (
    M.isStringLiteral(node) ||
    M.isNoSubstitutionTemplateLiteral(node) ||
    M.isNumericLiteral(node)
  ) {
    return node.getLiteralValue();
  }
  return undefined;
}

/** Returns true when the kinds differ in a known, harmless way. */
function compareKind(m: MorphNode, n: Node, at: string, out: Mismatches): boolean {
  if (m.getKindName() === kindName(n)) return false;
  if (KNOWN_KIND_PAIRS.has(`${m.getKindName()}>${kindName(n)}`)) return true;
  out.check(at, "kind", m.getKindName(), kindName(n));
  return false;
}

function comparePositions(
  m: MorphNode,
  n: Node,
  sf: SourceFile,
  at: string,
  out: Mismatches
): void {
  out.check(at, "text", m.getText(), textOf(n, sf));
  out.check(at, "start", m.getStart(), startOf(n, sf));
  out.check(at, "startLine", m.getStartLineNumber(), startLine(n, sf));
  out.check(at, "startLinePos", m.getStartLinePos(), startLinePos(n, sf));
  out.check(
    at,
    "lineAndColumn",
    m.getSourceFile().getLineAndColumnAtPos(m.getStart()),
    lineAndColumn(sf, n.getStart(sf))
  );
}

function compareContent(m: MorphNode, n: Node, sf: SourceFile, at: string, out: Mismatches): void {
  out.check(at, "literal", morphLiteral(m), literalValue(n));
  out.check(at, "name", morphName(m), ts7Name(n));
  const morphDocs = M.isJSDocable(m) ? m.getJsDocs() : [];
  out.check(
    at,
    "jsDocs",
    morphDocs.map((d) => [d.getDescription(), d.getText()]),
    jsDocs(n).map((d) => [jsDocDescription(d, sf), jsDocText(d, sf)])
  );
  if (M.isVariableDeclarationList(m) && isVariableDeclarationList(n)) {
    out.check(at, "declarationKind", m.getDeclarationKind(), declarationKind(n));
  }
}

const isFunctionLike = (node: Node): node is Node =>
  isFunctionDeclaration(node) || isArrowFunction(node) || isFunctionExpression(node);

function compareLookups(m: MorphNode, n: Node, sf: SourceFile, at: string, out: Mismatches): void {
  if (M.isObjectLiteralExpression(m) && isObjectLiteralExpression(n)) {
    const names = m.getProperties().flatMap((p) => (M.isSpreadAssignment(p) ? [] : [p.getName()]));
    for (const name of [...names, "missing"]) {
      out.check(
        at,
        `objectProperty(${name})`,
        m.getProperty(name)?.getStart(),
        objectProperty(n, name)?.getStart(sf)
      );
    }
  }
  if (M.isCallExpression(m) && isCallExpression(n)) {
    const expected = m
      .getFirstAncestor(
        (x) => M.isFunctionDeclaration(x) || M.isArrowFunction(x) || M.isFunctionExpression(x)
      )
      ?.getStart();
    out.check(at, "firstAncestor", expected, firstAncestor(n, isFunctionLike)?.getStart(sf));
  }
  if (M.isFunctionDeclaration(m) || M.isArrowFunction(m)) {
    const expected = m.getFirstDescendant((x) => M.isCallExpression(x))?.getStart();
    out.check(at, "firstDescendant", expected, firstDescendant(n, isCallExpression)?.getStart(sf));
  }
}

function compareStatements(pair: FilePair, out: Mismatches): void {
  const { where, morph, ts7 } = pair;
  out.check(
    where,
    "typeAliases",
    morph.getTypeAliases().map((t) => t.getName()),
    typeAliases(ts7).map(nameOf)
  );
  for (const alias of morph.getTypeAliases()) {
    out.check(
      where,
      `typeAlias(${alias.getName()})`,
      alias.getStart(),
      typeAlias(ts7, alias.getName())?.getStart(ts7)
    );
  }
  out.check(
    where,
    "functions",
    morph.getFunctions().map((f) => [f.getName(), f.getStart(), f.hasExportKeyword()]),
    functionDeclarations(ts7).map((f) => [nameOf(f), f.getStart(ts7), hasExportKeyword(f)])
  );
  for (const name of morph.getFunctions().map((f) => f.getName() ?? "")) {
    out.check(
      where,
      `function(${name})`,
      morph.getFunction(name)?.getStart(),
      functionDeclaration(ts7, name)?.getStart(ts7)
    );
  }
  out.check(
    where,
    "variableStatements",
    morph.getVariableStatements().map((s) => [s.getStart(), s.hasExportKeyword()]),
    variableStatements(ts7).map((s) => [s.getStart(ts7), hasExportKeyword(s)])
  );
  const names = [
    ...morph.getVariableDeclarations().map((d) => d.getName()),
    "picked",
    "renamedPick",
    "missing",
  ];
  for (const name of names) {
    out.check(
      where,
      `variableDeclaration(${name})`,
      morph.getVariableDeclaration(name)?.getStart(),
      variableDeclaration(ts7, name)?.getStart(ts7)
    );
  }
  out.check(
    where,
    "imports",
    morph
      .getImportDeclarations()
      .map((d) => [d.getModuleSpecifierValue(), d.getNamedImports().map((s) => s.getName())]),
    importDeclarations(ts7).map((d) => [moduleSpecifierValue(d), namedImports(d).map(importedName)])
  );
  out.check(
    where,
    "leadingComments",
    morph.getStatements().map((s) => s.getLeadingCommentRanges().map((r) => r.getText())),
    ts7.statements.map((s) => leadingComments(s, ts7).map((r) => r.text))
  );
}

function edgePair(): FilePair {
  const pair = pairs.find((p) => p.where === "edge:edge.ts");
  if (!pair) throw new Error("edge.ts missing");
  return pair;
}

describe("ast helpers match ts-morph node by node", () => {
  test("walk order, kind, text, positions, lines, literals, names, JSDoc, declaration kind", () => {
    const out = new Mismatches();
    let compared = 0;
    let knownKindDiffs = 0;
    for (const pair of pairs) {
      for (const [m, n] of zipped(pair, out)) {
        compared++;
        const at = `${pair.where}@${m.getStart()} ${m.getKindName()}`;
        if (compareKind(m, n, at, out)) knownKindDiffs++;
        comparePositions(m, n, pair.ts7, at, out);
        compareContent(m, n, pair.ts7, at, out);
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
      for (const [m, n] of zipped(pair, out)) {
        if (M.isObjectLiteralExpression(m)) objects++;
        compareLookups(m, n, pair.ts7, `${pair.where}@${m.getStart()}`, out);
      }
    }
    expect(out.head()).toEqual([]);
    expect(objects).toBeGreaterThan(50);
  });

  test("forEachDescendant stops on a truthy callback value, as ts-morph does", () => {
    const pair = edgePair();
    let morphVisited = 0;
    const morphHit = pair.morph.forEachDescendant((node) => {
      morphVisited++;
      return M.isCallExpression(node) ? node.getText() : undefined;
    });
    let visited = 0;
    const hit = forEachDescendant(pair.ts7, (node) => {
      visited++;
      return isCallExpression(node) ? textOf(node, pair.ts7) : undefined;
    });
    expect(hit).toBe(morphHit);
    expect(visited).toBe(morphVisited);
    expect(visited).toBeLessThan(ts7Descendants(pair.ts7).length);
  });

  test("the edge project exercises what it claims to", () => {
    const { ts7, morph } = edgePair();
    expect(ts7.text.includes("\r/")).toBe(true);
    expect(ts7.text.includes(" ")).toBe(true);
    // TS 7's own line map breaks on the CR and the U+2028; ts-morph (and startLine) do not.
    const last = ts7.statements.at(-1);
    if (!last) throw new Error("no statements");
    const ts7Line = ts7.getLineAndCharacterOfPosition(last.getStart(ts7)).line + 1;
    expect(startLine(last, ts7)).toBe(ts7Line - 2);
    const description = jsDocs(functionDeclaration(ts7, "documented")).map((d) =>
      jsDocDescription(d, ts7)
    );
    expect(description).toEqual(
      morph
        .getFunctionOrThrow("documented")
        .getJsDocs()
        .map((d) => d.getDescription())
    );
    expect(description[0]).toContain("description\nsecond line");
  });
});
