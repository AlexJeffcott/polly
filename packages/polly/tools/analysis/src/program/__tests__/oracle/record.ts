// Recorded the program-module oracle from ts-morph 28 (TS 6.0), once, before
// ts-morph was removed: `bun tools/analysis/src/program/__tests__/oracle/record.ts`
// from packages/polly. It mirrors the ts-morph half of ast.test.ts and
// program.test.ts as they stood when ts-morph was the live reference, call
// for call and in the same order (union member order follows type-creation
// order, so the order of checker questions is part of the answer).
//
// Writes snapshot.json (the frozen input texts), ast.json and program.json.

import * as fs from "node:fs";
import { createRequire } from "node:module";
import * as os from "node:os";
import * as path from "node:path";
import {
  Node as M,
  type Node as MorphNode,
  type SourceFile as MorphSourceFile,
  type Type as MorphType,
  Project,
} from "ts-morph";
import {
  type Corpora,
  type CorpusName,
  ORACLE_DIR,
  REPO_ROOT,
  SNAPSHOT_TSCONFIGS,
  sha256,
  writeCorpora,
} from "../corpus";

// ---------------------------------------------------------------- snapshot

function recordSnapshot(): Record<string, string> {
  const files: Record<string, string> = {};
  for (const tsconfig of Object.values(SNAPSHOT_TSCONFIGS)) {
    const absolute = path.join(REPO_ROOT, tsconfig);
    files[tsconfig] = fs.readFileSync(absolute, "utf8");
    for (const file of new Project({ tsConfigFilePath: absolute }).getSourceFiles()) {
      const rel = path.relative(REPO_ROOT, file.getFilePath());
      if (rel.startsWith("..") || rel.includes("node_modules")) throw new Error(rel);
      files[rel] = fs.readFileSync(file.getFilePath(), "utf8");
    }
  }
  // Each package.json above a file: a workspace package resolves through its exports.
  for (const file of Object.keys(files)) {
    for (let dir = path.dirname(file); dir !== "."; dir = path.dirname(dir)) {
      const manifest = path.join(dir, "package.json");
      if (fs.existsSync(path.join(REPO_ROOT, manifest))) {
        files[manifest] = fs.readFileSync(path.join(REPO_ROOT, manifest), "utf8");
      }
    }
  }
  return Object.fromEntries(Object.entries(files).sort(([a], [b]) => (a < b ? -1 : 1)));
}

// ---------------------------------------------------------------- ast.json

const DEFAULT_LIB = /\/lib\.[^/]*\.d\.ts$/;

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

type Extra = Record<string, unknown>;

function nodeExtra(m: MorphNode): Extra {
  const x: Extra = {};
  const literal = morphLiteral(m);
  if (literal !== undefined) x["l"] = literal;
  const name = morphName(m);
  if (name !== undefined) x["n"] = name;
  const docs = M.isJSDocable(m) ? m.getJsDocs() : [];
  if (docs.length > 0) x["d"] = docs.map((d) => [d.getDescription(), d.getText()]);
  if (M.isVariableDeclarationList(m)) x["k"] = m.getDeclarationKind();
  if (M.isObjectLiteralExpression(m)) {
    const names = m.getProperties().flatMap((p) => (M.isSpreadAssignment(p) ? [] : [p.getName()]));
    x["o"] = [...names, "missing"].map((n) => [n, m.getProperty(n)?.getStart() ?? null]);
  }
  if (M.isCallExpression(m)) {
    x["a"] =
      m
        .getFirstAncestor(
          (y) => M.isFunctionDeclaration(y) || M.isArrowFunction(y) || M.isFunctionExpression(y)
        )
        ?.getStart() ?? null;
  }
  if (M.isFunctionDeclaration(m) || M.isArrowFunction(m)) {
    x["f"] = m.getFirstDescendant((y) => M.isCallExpression(y))?.getStart() ?? null;
  }
  return x;
}

function statements(morph: MorphSourceFile): Extra {
  const names = [
    ...morph.getVariableDeclarations().map((d) => d.getName()),
    "picked",
    "renamedPick",
    "missing",
  ];
  return {
    typeAliases: morph.getTypeAliases().map((t) => [t.getName(), t.getStart()]),
    functions: morph.getFunctions().map((f) => [f.getName(), f.getStart(), f.hasExportKeyword()]),
    functionLookups: morph
      .getFunctions()
      .map((f) => f.getName() ?? "")
      .map((n) => [n, morph.getFunction(n)?.getStart() ?? null]),
    variableStatements: morph
      .getVariableStatements()
      .map((s) => [s.getStart(), s.hasExportKeyword()]),
    variableLookups: names.map((n) => [n, morph.getVariableDeclaration(n)?.getStart() ?? null]),
    imports: morph
      .getImportDeclarations()
      .map((d) => [d.getModuleSpecifierValue(), d.getNamedImports().map((s) => s.getName())]),
    leadingComments: morph
      .getStatements()
      .map((s) => s.getLeadingCommentRanges().map((r) => r.getText())),
  };
}

function recordAst(corpora: Corpora): Record<string, unknown> {
  const kinds: string[] = [];
  const kindIndex = (name: string): number => {
    let i = kinds.indexOf(name);
    if (i < 0) i = kinds.push(name) - 1;
    return i;
  };
  const files: unknown[] = [];
  let edgeFile: MorphSourceFile | undefined;
  for (const corpus of ["edge", "types-corpus", "full-featured"] as const) {
    const project = new Project({ tsConfigFilePath: corpora.tsconfig(corpus) });
    for (const file of project.getSourceFiles()) {
      const text = file.getFullText();
      const nodes: number[][] = [];
      const extra: Record<number, Extra> = {};
      file.forEachDescendant((m) => {
        const start = m.getStart();
        const t = m.getText();
        if (text.slice(start, start + t.length) !== t) throw new Error("text is not a slice");
        const lc = file.getLineAndColumnAtPos(start);
        const x = nodeExtra(m);
        if (Object.keys(x).length > 0) extra[nodes.length] = x;
        nodes.push([
          kindIndex(m.getKindName()),
          start,
          t.length,
          m.getStartLineNumber(),
          m.getStartLinePos(),
          lc.line,
          lc.column,
        ]);
      });
      const rel = corpora.rel(file.getFilePath());
      if (rel === "<edge>/src/edge.ts") edgeFile = file;
      files.push({
        corpus,
        path: rel,
        sha: sha256(text),
        nodes,
        extra,
        statements: statements(file),
      });
    }
  }
  if (!edgeFile) throw new Error("edge.ts missing");
  let visited = 0;
  const hit = edgeFile.forEachDescendant((node) => {
    visited++;
    return M.isCallExpression(node) ? node.getText() : undefined;
  });
  return {
    kinds,
    files,
    forEachStop: { hit, visited },
    documented: edgeFile
      .getFunctionOrThrow("documented")
      .getJsDocs()
      .map((d) => d.getDescription()),
  };
}

// ---------------------------------------------------------------- program.json

function inPathOrder(project: Project): MorphSourceFile[] {
  return [...project.getSourceFiles()].sort((a, b) => {
    const left = a.getFilePath();
    const right = b.getFilePath();
    return left < right ? -1 : left > right ? 1 : 0;
  });
}

function canonicalUnionText(text: string, members: readonly string[]): string {
  return members.length > 0 ? [...members].sort().join(" | ") : text;
}

function textTokens(text: string): string[] {
  return text
    .split(/[\s|;,{}()<>[\]:?]+/)
    .filter(Boolean)
    .sort();
}

function predicates(t: MorphType): boolean[] {
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

function typeLiteral(t: MorphType): string | number | null {
  const value = t.getLiteralValue();
  return typeof value === "string" || typeof value === "number" ? value : null;
}

function declaredInDefaultLib(type: MorphType): boolean {
  return (type.getSymbol()?.getDeclarations() ?? []).some((d) =>
    DEFAULT_LIB.test(d.getSourceFile().getFilePath())
  );
}

interface MorphRow {
  where: string;
  object: boolean;
  type: MorphType;
}

/** program.test.ts typeRows + compareTypeShape/Structure/Properties, ts-morph half. */
function recordTypeRows(corpora: Corpora, corpus: CorpusName): unknown[] {
  const morph = new Project({ tsConfigFilePath: corpora.tsconfig(corpus) });
  const anchor = inPathOrder(morph)[0];
  if (!anchor) throw new Error("empty project");
  const rows: MorphRow[] = [];
  for (const file of inPathOrder(morph)) {
    for (const alias of file.getTypeAliases()) {
      const where = `${corpora.rel(file.getFilePath())}:${alias.getName()}`;
      const type = alias.getType();
      const object = type.isObject();
      rows.push({ where, object, type });
      if (object) {
        for (const prop of type.getProperties()) {
          const propType = prop.getTypeAtLocation(anchor);
          rows.push({ where: `${where}.${prop.getName()}`, object: false, type: propType });
        }
      }
    }
  }
  const text = (t: MorphType): string => corpora.relText(t.getText());
  const optionalText = (t: MorphType | undefined): string | null => (t ? text(t) : null);
  return rows.map(({ where, object, type: m }) => {
    const unionMembers = m.getUnionTypes().map((u) => text(u));
    const shape = {
      text: textTokens(canonicalUnionText(text(m), unionMembers)),
      unionMembers,
      predicates: predicates(m),
      literal: typeLiteral(m),
      nullable: m.isNullable(),
      symbol: m.getSymbol()?.getName() ?? null,
    };
    const declared = m.getAliasSymbol()?.getDeclaredType();
    const structure = {
      arrayElement: optionalText(m.getArrayElementType()),
      typeArguments: (m.isObject() ? m.getTypeArguments() : []).map((a) => text(a)),
      aliasDeclaredType: declared
        ? canonicalUnionText(
            text(declared),
            declared.getUnionTypes().map((u) => text(u))
          )
        : null,
    };
    let props: Extra | null = null;
    if (m.isObject() && !m.isArray() && !declaredInDefaultLib(m)) {
      const first = m.getProperties()[0];
      props = {
        names: m.getProperties().map((p) => p.getName()),
        first: first
          ? {
              name: first.getName(),
              predicates: predicates(first.getTypeAtLocation(anchor)),
              isUnion: first.getTypeAtLocation(anchor).isUnion(),
            }
          : null,
      };
    }
    return { where, object, shape, structure, props };
  });
}

function recordUnionOrder(corpora: Corpora): unknown {
  const stateFile = path.join(corpora.edge.root, "src/state.ts");
  const ask = (names: string[]) => {
    const morph = new Project({ tsConfigFilePath: corpora.edge.tsconfig }).getSourceFileOrThrow(
      stateFile
    );
    return Object.fromEntries(
      names.map((name) => [
        name,
        morph
          .getTypeAliasOrThrow(name)
          .getType()
          .getUnionTypes()
          .map((u) => u.getText()),
      ])
    );
  };
  return { statusFirst: ask(["Status", "Num"]), laterFirst: ask(["Later", "Status"]) };
}

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

function recordProgram(corpora: Corpora): Record<string, unknown> {
  const projects = new Map<CorpusName, Project>();
  const load = (name: CorpusName): Project => {
    let p = projects.get(name);
    if (!p) {
      p = new Project({ tsConfigFilePath: corpora.tsconfig(name) });
      projects.set(name, p);
    }
    return p;
  };
  const rel = (f: MorphSourceFile) => corpora.rel(f.getFilePath());
  const three: CorpusName[] = ["edge", "types-corpus", "full-featured"];

  const files = Object.fromEntries(three.map((c) => [c, inPathOrder(load(c)).map(rel)]));
  const configFilePath = corpora.rel(
    String(load("types-corpus").getCompilerOptions()["configFilePath"])
  );

  const globs = ["**/state*.ts", "**/message*.ts", "src/**/*.ts", "**/*.tsx", "./src/*.ts", "**"];
  const previous = process.cwd();
  const matching: Record<string, Record<string, Record<string, string[]>>> = {};
  try {
    for (const c of three) {
      matching[c] = {};
      const dir = path.dirname(corpora.tsconfig(c));
      for (const [key, cwd] of [
        [".", dir],
        ["src", path.join(dir, "src")],
      ] as const) {
        process.chdir(cwd);
        const byGlob: Record<string, string[]> = {};
        for (const glob of globs) byGlob[glob] = load(c).getSourceFiles(glob).map(rel).sort();
        const perCorpus = matching[c];
        if (perCorpus) perCorpus[key] = byGlob;
      }
    }
  } finally {
    process.chdir(previous);
  }

  const { minimatch } = createRequire(require.resolve("ts-morph"))("minimatch");
  const cwd = "/work/proj";
  const globPaths = [
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
  const minimatchGlobs = [
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
  const minimatchResults = Object.fromEntries(
    minimatchGlobs.map((glob) => {
      const relative = glob.startsWith("./") ? glob.slice(2) : glob === "." ? "" : glob;
      const pattern = relative.startsWith("/") ? relative : relative ? `${cwd}/${relative}` : cwd;
      return [glob, globPaths.filter((p) => minimatch(p, pattern))];
    })
  );

  const typeRows = {
    "types-corpus": recordTypeRows(corpora, "types-corpus"),
    edge: recordTypeRows(corpora, "edge"),
  };
  const unionOrder = recordUnionOrder(corpora);

  const exportsByCorpus = Object.fromEntries(
    three.map((c) => [
      c,
      load(c)
        .getSourceFiles()
        .map((file) => ({
          path: rel(file),
          functions: file.getFunctions().map((fn) => {
            const r = fn.getReturnType();
            return [
              fn.getName() ?? null,
              corpora.relText(
                canonicalUnionText(
                  r.getText(),
                  r.getUnionTypes().map((u) => u.getText())
                )
              ),
              fn.isExported(),
            ];
          }),
          variables: file.getVariableStatements().map((s) => [s.getStart(), s.isExported()]),
        })),
    ])
  );

  const definitions = Object.fromEntries(
    (["edge", "full-featured"] as const).map((c) => [
      c,
      load(c)
        .getSourceFiles()
        .map((file) => {
          const out: Record<number, string[]> = {};
          file.forEachDescendant((node) => {
            if (!isMorphDefinitionSite(node) || !M.isIdentifier(node)) return;
            out[node.getStart()] = node
              .getDefinitionNodes()
              .filter(
                (d) =>
                  READ_KINDS.has(d.getKindName()) &&
                  !DEFAULT_LIB.test(d.getSourceFile().getFilePath())
              )
              .map(
                (d) =>
                  `${d.getKindName()}@${corpora.rel(d.getSourceFile().getFilePath())}:${d.getStart()}`
              )
              .sort();
          });
          return { path: rel(file), sites: out };
        }),
    ])
  );

  const imports = Object.fromEntries(
    (["full-featured", "todo-list", "edge"] as const).map((c) => [
      c,
      load(c)
        .getSourceFiles()
        .map((file) => ({
          path: rel(file),
          targets: file.getImportDeclarations().map((d) => {
            const target = d.getModuleSpecifierSourceFile()?.getFilePath();
            return [d.getModuleSpecifierValue(), target ? corpora.rel(target) : null];
          }),
        })),
    ])
  );

  return {
    files,
    configFilePath,
    matching,
    minimatch: { cwd, paths: globPaths, results: minimatchResults },
    typeRows,
    unionOrder,
    exports: exportsByCorpus,
    definitions,
    imports,
  };
}

// ---------------------------------------------------------------- main

const snapshot = recordSnapshot();
fs.mkdirSync(ORACLE_DIR, { recursive: true });
const note =
  "Recorded from ts-morph 28.0.0 (TypeScript 6.0) by oracle/record.ts; the reference answers for ast.test.ts and program.test.ts.";
fs.writeFileSync(
  path.join(ORACLE_DIR, "snapshot.json"),
  `${JSON.stringify({ note, files: snapshot })}\n`
);
const corpora = writeCorpora(snapshot);
try {
  fs.writeFileSync(
    path.join(ORACLE_DIR, "ast.json"),
    `${JSON.stringify({ note, ...recordAst(corpora) })}\n`
  );
  fs.writeFileSync(
    path.join(ORACLE_DIR, "program.json"),
    `${JSON.stringify({ note, ...recordProgram(corpora) })}\n`
  );
} finally {
  corpora.remove();
}
for (const name of ["ast.json", "program.json"]) {
  const recorded = fs.readFileSync(path.join(ORACLE_DIR, name), "utf8");
  if (recorded.includes(REPO_ROOT) || recorded.includes(fs.realpathSync(os.tmpdir()))) {
    throw new Error(`${name} names a file outside the frozen tree`);
  }
}
for (const name of ["snapshot.json", "ast.json", "program.json"]) {
  console.log(name, fs.statSync(path.join(ORACLE_DIR, name)).size);
}
