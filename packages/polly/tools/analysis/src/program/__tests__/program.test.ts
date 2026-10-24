// AnalysisProgram's files, glob, checker helpers, definitions and import
// targets, each checked against the answer ts-morph 28 gave on the same
// project (recorded in oracle/program.json, on the frozen corpora of ./corpus).

import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import * as path from "node:path";
import type { Node, SourceFile } from "typescript-7/ast";
import { isCallExpression, isIdentifier } from "typescript-7/ast/is";
import type { Type } from "typescript-7/async";
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
import { type Corpora, type CorpusName, Mismatches, readOracle, writeCorpora } from "./corpus";

/** Default-library files: ts-morph served its own bundled TS 6 copies, so answers there cannot agree. */
const DEFAULT_LIB = /\/lib\.[^/]*\.d\.ts$/;

interface TypeShape {
  text: string[];
  unionMembers: string[];
  predicates: boolean[];
  literal: string | number | null;
  nullable: boolean;
  symbol: string | null;
}

interface TypeStructure {
  arrayElement: string | null;
  typeArguments: string[];
  aliasDeclaredType: string | null;
}

interface TypeProps {
  names: string[];
  first: { name: string; predicates: boolean[]; isUnion: boolean } | null;
}

interface ExpectedTypeRow {
  where: string;
  object: boolean;
  shape: TypeShape;
  structure: TypeStructure;
  /** Absent for a non-object, an array, or a default-library type (not compared, as before). */
  props: TypeProps | null;
}

interface ProgramOracle {
  /** sourceFiles in path order, per corpus. */
  files: Record<string, string[]>;
  configFilePath: string;
  /** corpus -> cwd ("." or "src", relative to the tsconfig) -> glob -> files, sorted. */
  matching: Record<string, Record<string, Record<string, string[]>>>;
  minimatch: { cwd: string; paths: string[]; results: Record<string, string[]> };
  typeRows: Record<string, ExpectedTypeRow[]>;
  unionOrder: Record<"statusFirst" | "laterFirst", Record<string, string[]>>;
  exports: Record<
    string,
    {
      path: string;
      functions: [string | null, string, boolean][];
      variables: [number, boolean][];
    }[]
  >;
  definitions: Record<string, { path: string; sites: Record<string, string[]> }[]>;
  imports: Record<string, { path: string; targets: [string, string | null][] }[]>;
}

const oracle = readOracle<ProgramOracle>("program.json");
const session = new AnalysisSession();
let corpora: Corpora;
const loaded = new Map<string, AnalysisProgram>();

async function load(name: CorpusName): Promise<AnalysisProgram> {
  const tsconfig = corpora.tsconfig(name);
  const hit = loaded.get(tsconfig);
  if (hit) return hit;
  const program = await session.open(tsconfig);
  loaded.set(tsconfig, program);
  return program;
}

/** A recorded path back to the file it names in this run's temp dirs. */
function absolute(rel: string): string {
  return rel.startsWith("<edge>/")
    ? path.join(corpora.edge.root, rel.slice("<edge>/".length))
    : path.join(corpora.tree, rel);
}

const THREE: CorpusName[] = ["edge", "types-corpus", "full-featured"];

/** Each recorded file of a corpus with its TS 7 counterpart. */
async function filePairs<T extends { path: string }>(
  name: CorpusName,
  recorded: readonly T[]
): Promise<{ expected: T; ts7: SourceFile }[]> {
  const program = await load(name);
  return recorded.flatMap((expected) => {
    const ts7 = program.sourceFile(absolute(expected.path));
    return ts7 ? [{ expected, ts7 }] : [];
  });
}

const fileNames = (files: readonly { fileName: string }[]): string[] =>
  files.map((f) => corpora.rel(String(f.fileName)));

beforeAll(() => {
  corpora = writeCorpora();
});

afterAll(async () => {
  await session.close();
  corpora.remove();
});

describe("files", () => {
  test("sourceFiles is ts-morph's file set, in path order", async () => {
    for (const name of THREE) {
      expect(fileNames((await load(name)).sourceFiles)).toEqual(oracle.files[name] ?? ["missing"]);
    }
  }, 60_000);

  test("sourceFile(path), sourceFile(relative path) and sourceFile(bare name)", async () => {
    const program = await load("full-featured");
    const recorded = oracle.files["full-featured"] ?? [];
    expect(recorded.length).toBeGreaterThan(50);
    for (const rel of recorded) {
      expect(String(program.sourceFile(absolute(rel))?.fileName)).toBe(absolute(rel));
    }
    const first = absolute(recorded[0] ?? "");
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
    const program = await load("types-corpus");
    expect(corpora.rel(String(program.compilerOptions.configFilePath))).toBe(oracle.configFilePath);
  }, 60_000);

  test("sourceFilesMatching(glob, cwd) is ts-morph's getSourceFiles(glob) run from cwd", async () => {
    const out = new Mismatches();
    const previous = process.cwd();
    let compared = 0;
    try {
      for (const name of THREE) {
        const program = await load(name);
        const dir = path.dirname(corpora.tsconfig(name));
        for (const [key, byGlob] of Object.entries(oracle.matching[name] ?? {})) {
          const cwd = key === "." ? dir : path.join(dir, key);
          process.chdir(cwd);
          for (const [glob, expected] of Object.entries(byGlob)) {
            compared++;
            out.check(
              `${name} ${key} ${glob}`,
              "files",
              expected,
              fileNames(program.sourceFilesMatching(glob, cwd))
            );
          }
        }
      }
    } finally {
      process.chdir(previous);
    }
    expect(out.head()).toEqual([]);
    expect(compared).toBe(36);
    // The edge project's src/.hidden/state-shadow.ts is in the program but never matched.
    const program = await load("edge");
    expect(program.sourceFiles.some((f) => f.fileName.includes("/.hidden/"))).toBe(true);
    expect(
      program
        .sourceFilesMatching("**/state*.ts", corpora.edge.root)
        .map((f) => path.basename(f.fileName))
    ).toEqual(["state.ts"]);
  }, 60_000);
});

describe("createSourceGlob matches minimatch the way ts-morph called it", () => {
  const { cwd, paths, results } = oracle.minimatch;
  for (const [glob, expected] of Object.entries(results)) {
    test(glob, () => {
      const matches = createSourceGlob(glob, cwd);
      expect(paths.filter((p) => matches(p))).toEqual(expected);
    });
  }
  test("every recorded glob is checked", () => {
    expect(Object.keys(results).length).toBe(11);
  });
  test("unsupported syntax throws", () => {
    for (const glob of ["src/{a,b}.ts", "src/[ab].ts", "!src/*.ts", "src/@(a|b).ts"]) {
      expect(() => createSourceGlob(glob, cwd)).toThrow(/unsupported glob/);
    }
  });
});

// ---------------------------------------------------------------- checker

interface TypeRow {
  expected: ExpectedTypeRow;
  ts7: Type;
}

/**
 * Every type alias of a corpus and, one level down, each property of an
 * object alias, asked of a fresh checker (an isolated program) in the order
 * ts-morph was asked when the answers were recorded, as union member order
 * follows type-creation order.
 */
async function typeRows(name: CorpusName): Promise<{
  rows: TypeRow[];
  program: AnalysisProgram;
  anchor: SourceFile;
}> {
  const program = await session.openIsolated(corpora.tsconfig(name));
  const anchor = program.sourceFiles[0];
  if (!anchor) throw new Error("empty project");
  const expected = oracle.typeRows[name] ?? [];
  const rows: TypeRow[] = [];
  const next = (): ExpectedTypeRow => {
    const row = expected[rows.length];
    if (!row) throw new Error(`${name}: more type rows than recorded (${expected.length})`);
    return row;
  };
  for (const file of program.sourceFiles) {
    for (const decl of typeAliases(file)) {
      const row: TypeRow = { expected: next(), ts7: await program.typeOf(decl) };
      rows.push(row);
      if (!row.expected.object) continue;
      for (const p of await program.properties(row.ts7, anchor)) {
        rows.push({ expected: next(), ts7: p.type });
      }
    }
  }
  expect(rows.length).toBe(expected.length);
  return { rows, program, anchor };
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

const orUndefined = <T>(value: T | null | undefined): T | undefined => value ?? undefined;

/** `program.typeText`, with the paths in it normalised as the oracle stores them. */
const typeText = async (program: AnalysisProgram, t: Type): Promise<string> =>
  corpora.relText(await program.typeText(t));

const texts = (program: AnalysisProgram, types: readonly Type[]) =>
  Promise.all(types.map((t) => typeText(program, t)));

async function compareTypeShape(
  row: TypeRow,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const { expected, ts7: t } = row;
  const e = expected.shape;
  const where = expected.where;
  const members = await program.unionMembers(t);
  const memberTexts = await texts(program, members);
  out.check(
    where,
    "text",
    e.text,
    textTokens(canonicalUnionText(await typeText(program, t), memberTexts))
  );
  out.check(where, "unionMembers", e.unionMembers, memberTexts);
  out.check(where, "predicates", e.predicates, ts7Predicates(t));
  out.check(where, "literal", orUndefined(e.literal), typeLiteralValue(t));
  out.check(where, "nullable", e.nullable, await program.isNullable(t));
  out.check(where, "symbol", orUndefined(e.symbol), (await t.getSymbol())?.name);
}

async function compareTypeStructure(
  row: TypeRow,
  program: AnalysisProgram,
  out: Mismatches
): Promise<void> {
  const { expected, ts7: t } = row;
  const e = expected.structure;
  const where = expected.where;
  const element = await program.arrayElement(t);
  out.check(
    where,
    "arrayElement",
    orUndefined(e.arrayElement),
    element && (await typeText(program, element))
  );
  out.check(
    where,
    "typeArguments",
    e.typeArguments,
    await texts(program, await program.typeArguments(t))
  );
  const declared = await program.aliasDeclaredType(t);
  out.check(
    where,
    "aliasDeclaredType",
    orUndefined(e.aliasDeclaredType),
    declared &&
      canonicalUnionText(await typeText(program, declared), [
        ...(await texts(program, await program.unionMembers(declared))),
      ])
  );
}

async function compareProperties(
  row: TypeRow,
  program: AnalysisProgram,
  anchor: SourceFile,
  out: Mismatches
): Promise<void> {
  const { expected, ts7: t } = row;
  const e = expected.props;
  const where = expected.where;
  if (!e) return;
  const props = await program.properties(t, anchor);
  out.check(
    where,
    "properties",
    e.names,
    props.map((p) => p.name)
  );
  out.check(where, "propertyNames", e.names, await program.propertyNames(t));
  const symbols = await program.propertySymbols(t);
  out.check(
    where,
    "propertySymbols",
    e.names,
    symbols.map((s) => s.name)
  );
  const firstSymbol = symbols[0];
  if (e.first && firstSymbol) {
    out.check(
      where,
      "symbolTypeAt",
      e.first.predicates,
      ts7Predicates(await program.symbolTypeAt(firstSymbol, anchor))
    );
  }
  if (e.first) {
    const one = await program.property(t, e.first.name, anchor);
    out.check(where, "property", e.first.name, one?.name);
    out.check(where, "property type", e.first.isUnion, one && typeIs.union(one.type));
  }
  out.check(
    where,
    "property(missing)",
    undefined,
    await program.property(t, "__missing__", anchor)
  );
}

describe("checker helpers match ts-morph", () => {
  for (const name of ["types-corpus", "edge"] as const) {
    test(`${name}: typeText, unionMembers, predicates, properties, arrays, type arguments, aliases`, async () => {
      const { rows, program, anchor } = await typeRows(name);
      const out = new Mismatches();
      for (const row of rows) {
        await compareTypeShape(row, program, out);
        await compareTypeStructure(row, program, out);
        await compareProperties(row, program, anchor, out);
      }
      expect(out.head()).toEqual([]);
      expect(rows.length).toBeGreaterThan(10);
    }, 60_000);
  }

  test("unionMembers follows creation order, as TS 6 did, and openIsolated resets it", async () => {
    const stateFile = path.join(corpora.edge.root, "src/state.ts");
    /** Union member texts of each alias, asked in the given order, on a fresh program. */
    const ask = async (names: string[]) => {
      const program = await session.openIsolated(corpora.edge.tsconfig);
      const sf = program.sourceFile(stateFile);
      if (!sf) throw new Error("state.ts missing");
      const result: Record<string, { ts7: string[]; ts7Raw: string[] }> = {};
      for (const name of names) {
        const alias = typeAliases(sf).find((a) => a.name.text === name);
        if (!alias) throw new Error(name);
        const type = await program.typeOf(alias);
        result[name] = {
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
    for (const [run, recorded] of [
      [statusFirst, oracle.unionOrder.statusFirst],
      [laterFirst, oracle.unionOrder.laterFirst],
    ] as const) {
      expect(Object.keys(run)).toEqual(Object.keys(recorded));
      for (const [name, row] of Object.entries(run)) expect(row.ts7).toEqual(recorded[name] ?? []);
    }
  }, 60_000);
});

type ExportsFile = ProgramOracle["exports"][string][number];

/** Compare one file's recorded returnType / isExported answers; returns the functions compared. */
async function compareFileExports(
  where: string,
  expected: ExportsFile,
  ts7: SourceFile,
  program: AnalysisProgram,
  out: Mismatches
): Promise<number> {
  let functions = 0;
  const fns = functionDeclarations(ts7);
  out.check(where, "function count", expected.functions.length, fns.length);
  for (const [i, [fnName, returnText, exported]] of expected.functions.entries()) {
    const decl = fns[i];
    if (!decl) continue;
    functions++;
    const returnType = await program.returnType(decl);
    const members = await texts(program, await program.unionMembers(returnType));
    out.check(
      `${where}:${fnName}`,
      "returnType",
      returnText,
      canonicalUnionText(await typeText(program, returnType), members)
    );
    out.check(`${where}:${fnName}`, "isExported", exported, await program.isExported(decl));
  }
  const statements = variableStatements(ts7);
  out.check(where, "statement count", expected.variables.length, statements.length);
  for (const [i, [start, exported]] of expected.variables.entries()) {
    const decl = statements[i];
    if (!decl) continue;
    out.check(`${where}@${start}`, "isExported", exported, await program.isExported(decl));
  }
  return functions;
}

describe("returnType and isExported", () => {
  test("every function and variable statement of every corpus", async () => {
    const out = new Mismatches();
    let functions = 0;
    for (const name of THREE) {
      const program = await load(name);
      for (const { expected, ts7 } of await filePairs(name, oracle.exports[name] ?? [])) {
        functions += await compareFileExports(
          `${name}:${expected.path}`,
          expected,
          ts7,
          program,
          out
        );
      }
    }
    expect(out.head()).toEqual([]);
    expect(functions).toBeGreaterThan(100);
  }, 60_000);

  test("each export form in the edge project", async () => {
    const program = await load("edge");
    const sf = program.sourceFile(path.join(corpora.edge.root, "src/edge.ts"));
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

function ts7Definitions(program: AnalysisProgram, sf: SourceFile): Record<string, string[]> {
  const out: Record<string, string[]> = {};
  forEachDescendant(sf, (node) => {
    if (!isDefinitionSite(node)) return;
    out[String(startOf(node, sf))] = program
      .definitionNodes(node)
      .filter((d) => READ_KINDS.has(kindName(d)) && !DEFAULT_LIB.test(d.getSourceFile().fileName))
      .map((d) => `${kindName(d)}@${corpora.rel(d.getSourceFile().fileName)}:${startOf(d)}`)
      .sort();
  });
  return out;
}

async function compareImports(
  name: CorpusName,
  out: Mismatches
): Promise<{ imports: number; external: number }> {
  const program = await load(name);
  await program.prefetchImports();
  let imports = 0;
  let external = 0;
  for (const { expected, ts7 } of await filePairs(name, oracle.imports[name] ?? [])) {
    const decls = importDeclarations(ts7);
    out.check(expected.path, "import count", expected.targets.length, decls.length);
    for (const [i, [specifier, target]] of expected.targets.entries()) {
      const ours = decls[i];
      if (!ours) continue;
      imports++;
      const actual = program.moduleSpecifierSourceFile(ours)?.fileName;
      if (actual?.includes("/node_modules/")) external++;
      out.check(
        `${expected.path} ${specifier}`,
        "target",
        orUndefined(target),
        actual && corpora.rel(actual)
      );
    }
  }
  return { imports, external };
}

describe("prefetched lookups match ts-morph", () => {
  for (const name of ["edge", "full-featured"] as const) {
    test(`${name}: definitionNodes vs getDefinitionNodes on every definition site`, async () => {
      const program = await load(name);
      await program.prefetchDefinitions();
      const out = new Mismatches();
      let sites = 0;
      for (const { expected, ts7 } of await filePairs(name, oracle.definitions[name] ?? [])) {
        const actual = ts7Definitions(program, ts7);
        sites += Object.keys(actual).length;
        out.check(expected.path, "definitions", expected.sites, actual);
      }
      expect(out.head()).toEqual([]);
      expect(sites).toBeGreaterThan(name === "edge" ? 10 : 300);
    }, 120_000);
  }

  test("definitionNodes throws for an identifier that was not prefetched", async () => {
    const program = await load("edge");
    const sf = program.sourceFile(path.join(corpora.edge.root, "src/edge.ts"));
    const name = sf ? functionDeclarations(sf)[0]?.name : undefined;
    if (!name) throw new Error("no function");
    expect(() => program.definitionNodes(name)).toThrow(/not prefetched/);
    await program.prefetchDefinitions([name]);
    expect(program.definitionNodes(name).map(kindName)).toEqual(["FunctionDeclaration"]);
  }, 60_000);

  test("callee identifiers resolve across an import", async () => {
    const program = await load("edge");
    await program.prefetchDefinitions();
    const sf = program.sourceFile(path.join(corpora.edge.root, "src/edge.ts"));
    if (!sf) throw new Error("edge.ts missing");
    const resolved: string[] = [];
    forEachDescendant(sf, (node: Node) => {
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

  for (const name of ["full-featured", "todo-list", "edge"] as const) {
    test(`${name}: moduleSpecifierSourceFile vs getModuleSpecifierSourceFile`, async () => {
      const out = new Mismatches();
      const { imports, external } = await compareImports(name, out);
      expect(out.head()).toEqual([]);
      expect(imports).toBeGreaterThan(name === "edge" ? 2 : 20);
      if (name !== "edge") expect(external).toBeGreaterThan(0);
    }, 120_000);
  }
});
