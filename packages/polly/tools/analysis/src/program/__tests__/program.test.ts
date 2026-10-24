// AnalysisProgram's files, glob, checker helpers, definitions and import
// targets, each checked against ts-morph's answer on the same project.

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import { createRequire } from "node:module";
import * as path from "node:path";
import {
  Node as M,
  type FunctionDeclaration as MorphFunction,
  type Node as MorphNode,
  type SourceFile as MorphSourceFile,
  type Type as MorphType,
  Project,
} from "ts-morph";
import type { Node, SourceFile } from "typescript-7/ast";
import { isCallExpression, isIdentifier } from "typescript-7/ast/is";
import type { Type } from "typescript-7/async";
import { sourceFilesInPathOrder } from "../../extract/source-file-order";
import { type AnalysisProgram, AnalysisSession, isDefinitionSite } from "../analysis-program";
import {
  forEachDescendant,
  functionDeclarations,
  importDeclarations,
  kindName,
  startOf,
  typeAliases,
  variableStatements,
} from "../ast";
import { createSourceGlob } from "../glob";
import { typeIs, typeLiteralValue } from "../type-flags";
import { FULL_FEATURED, Mismatches, TODO_LIST, TYPES_CORPUS, writeEdgeProject } from "./corpus";

/** Default-library files: ts-morph serves its own bundled TS 6 copies, so answers there cannot agree. */
const DEFAULT_LIB = /\/lib\.[^/]*\.d\.ts$/;

const session = new AnalysisSession();
let edge = { tsconfig: "", root: "" };
const loaded = new Map<string, { morph: Project; program: AnalysisProgram }>();

async function load(tsconfig: string): Promise<{ morph: Project; program: AnalysisProgram }> {
  const hit = loaded.get(tsconfig);
  if (hit) return hit;
  const entry = {
    morph: new Project({ tsConfigFilePath: tsconfig }),
    program: await session.open(tsconfig),
  };
  loaded.set(tsconfig, entry);
  return entry;
}

const corpora = (): [string, string][] => [
  ["edge", edge.tsconfig],
  ["types-corpus", TYPES_CORPUS],
  ["full-featured", FULL_FEATURED],
];

/** Each ts-morph source file with its TS 7 counterpart. */
async function filePairs(tsconfig: string): Promise<{ morph: MorphSourceFile; ts7: SourceFile }[]> {
  const { morph, program } = await load(tsconfig);
  return morph.getSourceFiles().flatMap((file) => {
    const ts7 = program.sourceFile(file.getFilePath());
    return ts7 ? [{ morph: file, ts7 }] : [];
  });
}

const fileNames = (files: readonly { fileName: string }[]): string[] =>
  files.map((f) => String(f.fileName));

beforeAll(() => {
  edge = writeEdgeProject();
});

afterAll(async () => {
  await session.close();
  if (edge.root) fs.rmSync(edge.root, { recursive: true, force: true });
});

describe("files", () => {
  test("sourceFiles is ts-morph's file set, in path order", async () => {
    for (const [, tsconfig] of corpora()) {
      const { morph, program } = await load(tsconfig);
      expect(fileNames(program.sourceFiles)).toEqual(
        sourceFilesInPathOrder(morph).map((f) => String(f.getFilePath()))
      );
    }
  }, 60_000);

  test("sourceFile(path), sourceFile(relative path) and sourceFile(bare name)", async () => {
    const { morph, program } = await load(FULL_FEATURED);
    for (const file of morph.getSourceFiles()) {
      expect(String(program.sourceFile(file.getFilePath())?.fileName)).toBe(
        String(file.getFilePath())
      );
    }
    const first = String(sourceFilesInPathOrder(morph)[0]?.getFilePath());
    const relative = path.relative(process.cwd(), first);
    expect(String(program.sourceFile(relative)?.fileName)).toBe(first);
    expect(
      String(program.sourceFile(path.basename(first))?.fileName).endsWith(
        `/${path.basename(first)}`
      )
    ).toBe(true);
    expect(program.sourceFile("/no/such/file.ts")).toBeUndefined();
  }, 60_000);

  test("compilerOptions.configFilePath matches ts-morph", async () => {
    const { morph, program } = await load(TYPES_CORPUS);
    expect(String(program.compilerOptions.configFilePath)).toBe(
      String(morph.getCompilerOptions()["configFilePath"])
    );
  }, 60_000);

  test("sourceFilesMatching(glob, cwd) is ts-morph's getSourceFiles(glob) run from cwd", async () => {
    const globs = ["**/state*.ts", "**/message*.ts", "src/**/*.ts", "**/*.tsx", "./src/*.ts", "**"];
    const out = new Mismatches();
    const previous = process.cwd();
    try {
      for (const [, tsconfig] of corpora()) {
        const { morph, program } = await load(tsconfig);
        for (const cwd of [path.dirname(tsconfig), path.join(path.dirname(tsconfig), "src")]) {
          process.chdir(cwd);
          for (const glob of globs) {
            const expected = morph.getSourceFiles(glob).map((f) => String(f.getFilePath()));
            out.check(
              `${cwd} ${glob}`,
              "files",
              expected.sort(),
              fileNames(program.sourceFilesMatching(glob, cwd))
            );
          }
        }
      }
    } finally {
      process.chdir(previous);
    }
    expect(out.head()).toEqual([]);
    // The edge project's src/.hidden/state-shadow.ts is in the program but never matched.
    const { program } = await load(edge.tsconfig);
    expect(program.sourceFiles.some((f) => f.fileName.includes("/.hidden/"))).toBe(true);
    expect(
      program.sourceFilesMatching("**/state*.ts", edge.root).map((f) => path.basename(f.fileName))
    ).toEqual(["state.ts"]);
  }, 60_000);
});

describe("createSourceGlob matches minimatch the way ts-morph calls it", () => {
  const requireFromMorph = createRequire(require.resolve("ts-morph"));
  const { minimatch } = requireFromMorph("minimatch");
  const cwd = "/work/proj";
  const paths = [
    "/work/proj/state.ts",
    "/work/proj/src/state.ts",
    "/work/proj/src/app-state.ts",
    "/work/proj/src/stateful.ts",
    "/work/proj/src/state.tsx",
    "/work/proj/.x/state.ts",
    "/work/proj/src/.x/state.ts",
    "/work/proj/src/.state.ts",
    "/work/proj/src/STATE.ts",
    "/work/proj/a/b/c/message-types.ts",
    "/work/other/state.ts",
    "/work/state.ts",
    "/work/proj",
  ];
  const globs = [
    "**/state*.ts",
    "**/message*.ts",
    "src/*.ts",
    "./src/**/*.ts",
    "?rc/*.ts",
    "**",
    "/work/*/state.ts",
    "**/*state*.ts",
    "**/m*s*-*.ts",
    "src/*a*e.t?",
    ".",
  ];
  for (const glob of globs) {
    test(glob, () => {
      const relative = glob.startsWith("./") ? glob.slice(2) : glob === "." ? "" : glob;
      const pattern = relative.startsWith("/") ? relative : relative ? `${cwd}/${relative}` : cwd;
      const matches = createSourceGlob(glob, cwd);
      expect(paths.filter((p) => matches(p))).toEqual(paths.filter((p) => minimatch(p, pattern)));
    });
  }
  test("unsupported syntax throws", () => {
    for (const glob of ["src/{a,b}.ts", "src/[ab].ts", "!src/*.ts", "src/@(a|b).ts"]) {
      expect(() => createSourceGlob(glob, cwd)).toThrow(/unsupported glob/);
    }
  });
});

// ---------------------------------------------------------------- checker

interface TypeRow {
  where: string;
  morph: MorphType;
  ts7: Type;
}

/**
 * Every type alias of a corpus and, one level down, each property of an
 * object alias. Both sides start from a fresh checker (a new ts-morph
 * Project, an isolated program) and are asked in the same order, as union
 * member order follows type-creation order.
 */
async function typeRows(tsconfig: string): Promise<{
  rows: TypeRow[];
  program: AnalysisProgram;
  anchor: SourceFile;
  morphAnchor: MorphSourceFile;
}> {
  const morph = new Project({ tsConfigFilePath: tsconfig });
  const program = await session.openIsolated(tsconfig);
  const anchor = program.sourceFiles[0];
  const morphAnchor = sourceFilesInPathOrder(morph)[0];
  if (!anchor || !morphAnchor) throw new Error("empty project");
  const rows: TypeRow[] = [];
  for (const file of sourceFilesInPathOrder(morph)) {
    const ts7 = program.sourceFile(file.getFilePath());
    if (!ts7) continue;
    const aliases = typeAliases(ts7);
    for (const [i, alias] of file.getTypeAliases().entries()) {
      const decl = aliases[i];
      if (!decl) continue;
      const where = `${path.basename(file.getFilePath())}:${alias.getName()}`;
      const row: TypeRow = {
        where,
        morph: alias.getType(),
        ts7: await program.typeOf(decl),
      };
      rows.push(row);
      if (row.morph.isObject())
        rows.push(...(await propertyRows(row, program, anchor, morphAnchor)));
    }
  }
  return { rows, program, anchor, morphAnchor };
}

async function propertyRows(
  row: TypeRow,
  program: AnalysisProgram,
  anchor: SourceFile,
  morphAnchor: MorphSourceFile
): Promise<TypeRow[]> {
  const props = await program.properties(row.ts7, anchor);
  return row.morph.getProperties().flatMap((prop, j) => {
    const p = props[j];
    return p
      ? [
          {
            where: `${row.where}.${prop.getName()}`,
            morph: prop.getTypeAtLocation(morphAnchor),
            ts7: p.type,
          },
        ]
      : [];
  });
}

/**
 * Type text with union members in a canonical order. TS 7 prints a literal
 * union in value order, TS 6 in creation order; the members are the same.
 * Only the top-level union is canonicalised.
 */
function canonicalUnionText(text: string, members: readonly string[]): string {
  return members.length > 0 ? [...members].sort().join(" | ") : text;
}

/**
 * The text's tokens, sorted: TS 7 also prints unions nested inside a type
 * (`{ level: 1 | 2 | 3 }`) in value order, which nothing can undo short of
 * a printer of our own, so the comparison is order-insensitive below the top.
 */
function textTokens(text: string): string[] {
  return text
    .split(/[\s|;,{}()<>[\]:?]+/)
    .filter(Boolean)
    .sort();
}

function declaredInDefaultLib(type: MorphType): boolean {
  return (type.getSymbol()?.getDeclarations() ?? []).some((d) =>
    DEFAULT_LIB.test(d.getSourceFile().getFilePath())
  );
}

function morphPredicates(t: MorphType): boolean[] {
  return [
    t.isUnion(),
    t.isBoolean(),
    t.isBooleanLiteral(),
    t.isString(),
    t.isStringLiteral(),
    t.isNumber(),
    t.isNumberLiteral(),
    t.isObject(),
    t.isNull(),
    t.isUndefined(),
  ];
}

function ts7Predicates(t: Type): boolean[] {
  return [
    typeIs.union(t),
    typeIs.boolean(t),
    typeIs.booleanLiteral(t),
    typeIs.string(t),
    typeIs.stringLiteral(t),
    typeIs.number(t),
    typeIs.numberLiteral(t),
    typeIs.object(t),
    typeIs.null(t),
    typeIs.undefined(t),
  ];
}

function morphLiteral(t: MorphType): string | number | undefined {
  const value = t.getLiteralValue();
  return typeof value === "string" || typeof value === "number" ? value : undefined;
}

const texts = (program: AnalysisProgram, types: readonly Type[]) =>
  Promise.all(types.map((t) => program.typeText(t)));

async function compareTypeShape(
  row: TypeRow,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const { where, morph: m, ts7: t } = row;
  const members = await program.unionMembers(t);
  const memberTexts = await texts(program, members);
  const morphMembers = m.getUnionTypes().map((u) => u.getText());
  out.check(
    where,
    "text",
    textTokens(canonicalUnionText(m.getText(), morphMembers)),
    textTokens(canonicalUnionText(await program.typeText(t), memberTexts))
  );
  out.check(where, "unionMembers", morphMembers, memberTexts);
  out.check(where, "predicates", morphPredicates(m), ts7Predicates(t));
  out.check(where, "literal", morphLiteral(m), typeLiteralValue(t));
  out.check(where, "nullable", m.isNullable(), await program.isNullable(t));
  out.check(where, "symbol", m.getSymbol()?.getName(), (await t.getSymbol())?.name);
}

async function compareTypeStructure(
  row: TypeRow,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const { where, morph: m, ts7: t } = row;
  const element = await program.arrayElement(t);
  out.check(
    where,
    "arrayElement",
    m.getArrayElementType()?.getText(),
    element && (await program.typeText(element))
  );
  out.check(
    where,
    "typeArguments",
    (m.isObject() ? m.getTypeArguments() : []).map((a) => a.getText()),
    await texts(program, await program.typeArguments(t))
  );
  const declared = await program.aliasDeclaredType(t);
  const morphDeclared = m.getAliasSymbol()?.getDeclaredType();
  out.check(
    where,
    "aliasDeclaredType",
    morphDeclared &&
      canonicalUnionText(
        morphDeclared.getText(),
        morphDeclared.getUnionTypes().map((u) => u.getText())
      ),
    declared &&
      canonicalUnionText(await program.typeText(declared), [
        ...(await texts(program, await program.unionMembers(declared))),
      ])
  );
}

async function compareProperties(
  row: TypeRow,
  program: AnalysisProgram,
  anchor: SourceFile,
  morphAnchor: MorphSourceFile,
  out: Mismatches
): Promise<void> {
  const { where, morph: m, ts7: t } = row;
  if (!m.isObject() || m.isArray() || declaredInDefaultLib(m)) return;
  const props = await program.properties(t, anchor);
  out.check(
    where,
    "properties",
    m.getProperties().map((p) => p.getName()),
    props.map((p) => p.name)
  );
  const first = m.getProperties()[0];
  if (first) {
    const one = await program.property(t, first.getName(), anchor);
    out.check(where, "property", first.getName(), one?.name);
    out.check(
      where,
      "property type",
      first.getTypeAtLocation(morphAnchor).isUnion(),
      one && typeIs.union(one.type)
    );
  }
  out.check(
    where,
    "property(missing)",
    undefined,
    await program.property(t, "__missing__", anchor)
  );
}

describe("checker helpers match ts-morph", () => {
  for (const name of ["types-corpus", "edge"]) {
    test(`${name}: typeText, unionMembers, predicates, properties, arrays, type arguments, aliases`, async () => {
      const { rows, program, anchor, morphAnchor } = await typeRows(
        name === "edge" ? edge.tsconfig : TYPES_CORPUS
      );
      const out = new Mismatches();
      for (const row of rows) {
        await compareTypeShape(row, program, out);
        await compareTypeStructure(row, program, out);
        await compareProperties(row, program, anchor, morphAnchor, out);
      }
      expect(out.head()).toEqual([]);
      expect(rows.length).toBeGreaterThan(10);
    }, 60_000);
  }

  test("unionMembers follows creation order, as TS 6 did, and openIsolated resets it", async () => {
    const stateFile = path.join(edge.root, "src/state.ts");
    /** Union member texts of each alias, asked in the given order, on a fresh ts-morph Project and a fresh program. */
    const ask = async (names: string[]) => {
      const morph = new Project({ tsConfigFilePath: edge.tsconfig }).getSourceFileOrThrow(
        stateFile
      );
      const program = await session.openIsolated(edge.tsconfig);
      const sf = program.sourceFile(stateFile);
      if (!sf) throw new Error("state.ts missing");
      const result: Record<string, { tsMorph: string[]; ts7: string[]; ts7Raw: string[] }> = {};
      for (const name of names) {
        const alias = typeAliases(sf).find((a) => a.name.text === name);
        if (!alias) throw new Error(name);
        const type = await program.typeOf(alias);
        result[name] = {
          tsMorph: morph
            .getTypeAliasOrThrow(name)
            .getType()
            .getUnionTypes()
            .map((u) => u.getText()),
          ts7: await texts(program, await program.unionMembers(type)),
          ts7Raw: await texts(program, type.isUnionType() ? await type.getTypes() : []),
        };
      }
      return result;
    };
    const statusFirst = await ask(["Status", "Num"]);
    expect(statusFirst["Status"]?.ts7).toEqual(['"zeta"', '"alpha"', '"mid"']);
    expect(statusFirst["Status"]?.ts7Raw).toEqual(['"alpha"', '"mid"', '"zeta"']);
    expect(statusFirst["Num"]?.ts7).toEqual(["3", "1", "2", "-4"]);
    // `Later` creates "mid" and "zeta" first; both checkers then list Status by that history.
    const laterFirst = await ask(["Later", "Status"]);
    expect(laterFirst["Status"]?.ts7).toEqual(['"mid"', '"zeta"', '"alpha"']);
    for (const run of [statusFirst, laterFirst]) {
      for (const row of Object.values(run)) expect(row.ts7).toEqual(row.tsMorph);
    }
  }, 60_000);
});

async function compareFunction(
  where: string,
  fn: MorphFunction,
  ts7: Parameters<AnalysisProgram["isExported"]>[0] & Node,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const returnType = await program.returnType(ts7);
  const members = await texts(program, await program.unionMembers(returnType));
  const morphReturn = fn.getReturnType();
  out.check(
    where,
    "returnType",
    canonicalUnionText(
      morphReturn.getText(),
      morphReturn.getUnionTypes().map((u) => u.getText())
    ),
    canonicalUnionText(await program.typeText(returnType), members)
  );
  out.check(where, "isExported", fn.isExported(), await program.isExported(ts7));
}

async function compareFileExports(
  where: string,
  file: MorphSourceFile,
  ts7: SourceFile,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const fns = functionDeclarations(ts7);
  for (const [i, fn] of file.getFunctions().entries()) {
    const decl = fns[i];
    if (decl) await compareFunction(`${where}:${fn.getName()}`, fn, decl, program, out);
  }
  const statements = variableStatements(ts7);
  for (const [i, statement] of file.getVariableStatements().entries()) {
    const decl = statements[i];
    if (!decl) continue;
    const at = `${where}@${statement.getStart()}`;
    out.check(at, "isExported", statement.isExported(), await program.isExported(decl));
  }
}

describe("returnType and isExported", () => {
  test("every function and variable statement of every corpus", async () => {
    const out = new Mismatches();
    for (const [name, tsconfig] of corpora()) {
      const { program } = await load(tsconfig);
      for (const { morph: file, ts7 } of await filePairs(tsconfig)) {
        await compareFileExports(
          `${name}:${path.basename(file.getFilePath())}`,
          file,
          ts7,
          program,
          out
        );
      }
    }
    expect(out.head()).toEqual([]);
  }, 60_000);

  test("each export form in the edge project", async () => {
    const { program } = await load(edge.tsconfig);
    const sf = program.sourceFile(path.join(edge.root, "src/edge.ts"));
    if (!sf) throw new Error("edge.ts missing");
    const exported: string[] = [];
    for (const fn of functionDeclarations(sf)) {
      if (fn.name && (await program.isExported(fn))) exported.push(fn.name.text);
    }
    expect(exported.sort()).toEqual([
      "defaulted",
      "disposer",
      "documented",
      "local",
      "overloaded",
      "renamed",
    ]);
  }, 60_000);
});

// ---------------------------------------------------------------- prefetch

/** The kinds the extractors read from a definition (handlers.ts resolveFunctionReference, resolveImportedTypeGuard, extractFieldNames). */
const READ_KINDS = new Set([
  "FunctionDeclaration",
  "VariableDeclaration",
  "FunctionExpression",
  "ArrowFunction",
]);

function isMorphDefinitionSite(node: MorphNode): boolean {
  if (!M.isIdentifier(node)) return false;
  const parent = node.getParent();
  if (M.isCallExpression(parent) || M.isNewExpression(parent)) {
    return parent.getExpression() === node || parent.getArguments().includes(node);
  }
  return M.isPropertyAssignment(parent) && parent.getInitializer() === node;
}

/** ts-morph's definitions per definition-site start offset, in the kinds the extractors read. */
function morphDefinitions(file: MorphSourceFile): Map<number, string[]> {
  const out = new Map<number, string[]>();
  file.forEachDescendant((node) => {
    if (!isMorphDefinitionSite(node) || !M.isIdentifier(node)) return;
    const keys = node
      .getDefinitionNodes()
      .filter(
        (d) => READ_KINDS.has(d.getKindName()) && !DEFAULT_LIB.test(d.getSourceFile().getFilePath())
      )
      .map((d) => `${d.getKindName()}@${d.getSourceFile().getFilePath()}:${d.getStart()}`);
    out.set(node.getStart(), keys.sort());
  });
  return out;
}

function ts7Definitions(program: AnalysisProgram, sf: SourceFile): Map<number, string[]> {
  const out = new Map<number, string[]>();
  forEachDescendant(sf, (node) => {
    if (!isDefinitionSite(node)) return;
    const keys = program
      .definitionNodes(node)
      .filter((d) => READ_KINDS.has(kindName(d)) && !DEFAULT_LIB.test(d.getSourceFile().fileName))
      .map((d) => `${kindName(d)}@${d.getSourceFile().fileName}:${startOf(d)}`);
    out.set(startOf(node, sf), keys.sort());
  });
  return out;
}

async function compareImports(
  tsconfig: string,
  out: Mismatches
): Promise<{ imports: number; external: number }> {
  const { program } = await load(tsconfig);
  await program.prefetchImports();
  let imports = 0;
  let external = 0;
  for (const { morph: file, ts7 } of await filePairs(tsconfig)) {
    const decls = importDeclarations(ts7);
    for (const [i, decl] of file.getImportDeclarations().entries()) {
      const ours = decls[i];
      if (!ours) continue;
      imports++;
      const actual = program.moduleSpecifierSourceFile(ours)?.fileName;
      if (actual?.includes("/node_modules/")) external++;
      out.check(
        `${path.basename(file.getFilePath())} ${decl.getModuleSpecifierValue()}`,
        "target",
        decl.getModuleSpecifierSourceFile()?.getFilePath(),
        actual
      );
    }
  }
  return { imports, external };
}

describe("prefetched lookups match ts-morph", () => {
  for (const name of ["edge", "full-featured"]) {
    test(`${name}: definitionNodes vs getDefinitionNodes on every definition site`, async () => {
      const tsconfig = name === "edge" ? edge.tsconfig : FULL_FEATURED;
      const { program } = await load(tsconfig);
      await program.prefetchDefinitions();
      const out = new Mismatches();
      let sites = 0;
      for (const { morph: file, ts7 } of await filePairs(tsconfig)) {
        const expected = morphDefinitions(file);
        const actual = ts7Definitions(program, ts7);
        sites += actual.size;
        out.check(
          path.basename(file.getFilePath()),
          "definitions",
          Object.fromEntries(expected),
          Object.fromEntries(actual)
        );
      }
      expect(out.head()).toEqual([]);
      expect(sites).toBeGreaterThan(name === "edge" ? 10 : 300);
    }, 120_000);
  }

  test("definitionNodes throws for an identifier that was not prefetched", async () => {
    const { program } = await load(edge.tsconfig);
    const sf = program.sourceFile(path.join(edge.root, "src/edge.ts"));
    const name = sf ? functionDeclarations(sf)[0]?.name : undefined;
    if (!name) throw new Error("no function");
    expect(() => program.definitionNodes(name)).toThrow(/not prefetched/);
    await program.prefetchDefinitions([name]);
    expect(program.definitionNodes(name).map(kindName)).toEqual(["FunctionDeclaration"]);
  }, 60_000);

  test("callee identifiers resolve across an import", async () => {
    const { program } = await load(edge.tsconfig);
    await program.prefetchDefinitions();
    const sf = program.sourceFile(path.join(edge.root, "src/edge.ts"));
    if (!sf) throw new Error("edge.ts missing");
    const resolved: string[] = [];
    forEachDescendant(sf, (node) => {
      if (
        isCallExpression(node) &&
        isIdentifier(node.expression) &&
        node.expression.text === "helper"
      ) {
        resolved.push(
          ...program
            .definitionNodes(node.expression)
            .map((d) => `${kindName(d)}:${path.basename(d.getSourceFile().fileName)}`)
        );
      }
    });
    expect(resolved).toEqual(["FunctionDeclaration:other.ts"]);
  }, 60_000);

  for (const [name, tsconfig] of [
    ["full-featured", FULL_FEATURED],
    ["todo-list", TODO_LIST],
    ["edge", ""],
  ]) {
    test(`${name}: moduleSpecifierSourceFile vs getModuleSpecifierSourceFile`, async () => {
      const out = new Mismatches();
      const { imports, external } = await compareImports(tsconfig || edge.tsconfig, out);
      expect(out.head()).toEqual([]);
      expect(imports).toBeGreaterThan(name === "edge" ? 2 : 20);
      if (name !== "edge") expect(external).toBeGreaterThan(0);
    }, 120_000);
  }
});
