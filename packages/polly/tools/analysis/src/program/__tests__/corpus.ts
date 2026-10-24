// Shared corpora for the program-module tests. The expected answers were
// recorded once from ts-morph 28 (TS 6.0) and live in ./oracle/; the tests
// compare an AnalysisSession's answers against them.
//
// The inputs are frozen with the answers: the edge project is the text below,
// and the repository corpora (the types corpus, examples/full-featured,
// examples/todo-list and the polly sources they reach) are the texts in
// oracle/snapshot.json, written to a temp tree that mirrors the repository
// layout. Each node_modules directory of the repository is symlinked into the
// tree, so module resolution sees the same packages it saw at recording time.

import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

export const POLLY_ROOT = path.resolve(import.meta.dir, "../../../../..");
export const REPO_ROOT = path.resolve(POLLY_ROOT, "../..");
export const ORACLE_DIR = path.join(import.meta.dir, "oracle");
/** The live types corpus (session.test.ts; the oracle reads its snapshot). */
export const TYPES_CORPUS = path.join(
  POLLY_ROOT,
  "scripts/analysis-parity/fixtures/types-corpus/tsconfig.json"
);

/** Repository-relative tsconfig of each snapshot corpus. */
export const SNAPSHOT_TSCONFIGS = {
  "types-corpus": "packages/polly/scripts/analysis-parity/fixtures/types-corpus/tsconfig.json",
  "full-featured": "examples/full-featured/tsconfig.json",
  "todo-list": "examples/todo-list/tsconfig.json",
} as const;

export type CorpusName = "edge" | keyof typeof SNAPSHOT_TSCONFIGS;

const LS = "\u2028";

/**
 * Edge cases ts-morph and TS 7 could answer differently: multi-line JSDoc
 * with tags, `export { f }` / `export default f`, overloads, an ambient
 * function, `await using`, destructured dynamic imports, literal unions out
 * of value order, a lone CR line break and a U+2028 inside a string.
 */
const EDGE_FILES: Record<string, string> = {
  "src/other.ts": [
    "export function helper(n: number): number {",
    "  return n * 2;",
    "}",
    "export const lazy = (s: string): string => s.trim();",
    "export type Other = { id: number };",
    "export function isOther(x: unknown): x is Other {",
    "  return typeof x === 'object' && x !== null && 'id' in x;",
    "}",
    "",
  ].join("\n"),
  "src/state.ts": [
    'export type { Shadow } from "./.hidden/state-shadow";',
    'export type Status = "zeta" | "alpha" | "mid";',
    "export type Num = 3 | 1 | 2 | -4;",
    'export type Mixed = "b" | { kind: "obj" } | "a" | null;',
    "export type AppState = {",
    '  role: "admin" | "user" | "guest";',
    "  status: Status;",
    "  ids: readonly number[];",
    "  list: string[];",
    "  map: Map<string, Status>;",
    "  set: Set<number>;",
    "  maybe?: Status | undefined;",
    "  count: number | null;",
    "  flag: boolean;",
    "  nested: { on: boolean; level: 1 | 3 | 2 };",
    "  mixed: Mixed;",
    "};",
    'export type Later = "mid" | "zeta";',
    "",
  ].join("\n"),
  "src/.hidden/state-shadow.ts": "export type Shadow = { x: number };\n",
  "src/edge.ts": [
    'import { helper, isOther, type Other } from "./other";',
    'import * as ns from "./other";',
    'import type { AppState } from "./state";',
    "",
    "/**",
    " * Multi-line description",
    " * second line continues",
    " *",
    " * @flow demo",
    " * @trigger click",
    " */",
    "export function documented(a: number): string {",
    "  return String(helper(a));",
    "}",
    "",
    "function local(): void {}",
    "export { local };",
    "",
    "function renamed(): void {}",
    "export { renamed as alias };",
    "",
    "function defaulted(): number {",
    "  return 1;",
    "}",
    "export default defaulted;",
    "",
    "function hidden(): Other | undefined {",
    "  return undefined;",
    "}",
    "",
    "export function overloaded(a: string): string;",
    "export function overloaded(a: number): number;",
    "export function overloaded(a: string | number): string | number {",
    "  return a;",
    "}",
    "",
    "declare function ambient(x: unknown): x is string;",
    "declare function getRes(): AsyncDisposable & Disposable;",
    "",
    "/** Arrow, exported. */",
    "export const exportedArrow = (n: number) => n + 1;",
    "const privateArrow = () => 0;",
    "let mutable = 1;",
    "var legacy = 2;",
    "const { picked, other: renamedPick } = { picked: 1, other: 2 };",
    "",
    "// leading line comment",
    "/* block comment */",
    "export async function disposer(): Promise<void> {",
    "  await using r = getRes();",
    "  using s = getRes();",
    '  const { lazy } = await import("./other");',
    "  lazy(String(r) + String(s));",
    "  const table = { pick: lazy };",
    "  table.pick('x');",
    "  if (isOther(r) || ambient(s)) ns.helper(1);",
    "}",
    "",
    "const handleA = (state: AppState): AppState => state;",
    "const computed = 'c';",
    "const short = 1;",
    "export const handlers = {",
    '  "quoted": handleA,',
    "  plain: handleA,",
    "  [computed]: 1,",
    "  short,",
    "  ...{ spread: 2 },",
    "  method() {",
    "    return hidden();",
    "  },",
    "};",
    "",
    "export const withCr = 1;\r// after a lone CR",
    `export const lineSep = "a${LS}b";`,
    "export const afterSep = overloaded(1) + mutable + legacy + picked + renamedPick + privateArrow();",
    "",
  ].join("\n"),
};

function writeFiles(root: string, files: Record<string, string>): void {
  for (const [file, text] of Object.entries(files)) {
    const target = path.join(root, file);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, text);
  }
}

const tempRoot = (prefix: string): string =>
  fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), prefix));

/** Write the edge-case project into a fresh temp dir (symlinks resolved) and return its tsconfig. */
export function writeEdgeProject(): { tsconfig: string; root: string } {
  const root = tempRoot("polly-program-edge-");
  writeFiles(root, EDGE_FILES);
  const tsconfig = path.join(root, "tsconfig.json");
  fs.writeFileSync(
    tsconfig,
    JSON.stringify({
      compilerOptions: {
        target: "ESNext",
        module: "ESNext",
        moduleResolution: "bundler",
        lib: ["ESNext"],
        strict: true,
        noEmit: true,
        skipLibCheck: true,
      },
      include: ["src/**/*"],
    })
  );
  return { tsconfig, root };
}

/** The frozen repository texts, by repository-relative path (tsconfigs included). */
export function readSnapshot(): Record<string, string> {
  return readOracle<{ files: Record<string, string> }>("snapshot.json").files;
}

/**
 * Link `real` (a node_modules directory of the repository) into the tree at
 * `at`, entry by entry. A workspace package (an entry that resolves into the
 * repository outside any node_modules, like @fairfox/polly) is linked to the
 * tree's own copy of that package, so its frozen files are the ones read.
 */
function linkNodeModules(real: string, at: string, tree: string): void {
  fs.mkdirSync(at, { recursive: true });
  for (const entry of fs.readdirSync(real)) {
    const source = path.join(real, entry);
    if (entry.startsWith("@") && fs.statSync(source).isDirectory() && !isLink(source)) {
      linkNodeModules(source, path.join(at, entry), tree);
      continue;
    }
    const resolved = fs.realpathSync(source);
    const inRepo = path.relative(REPO_ROOT, resolved);
    const workspace = !inRepo.startsWith("..") && !inRepo.split(path.sep).includes("node_modules");
    fs.symlinkSync(workspace ? path.join(tree, inRepo) : source, path.join(at, entry));
  }
}

const isLink = (file: string): boolean => fs.lstatSync(file).isSymbolicLink();

/**
 * Write `files` into a fresh temp tree laid out like the repository and link
 * in the repository's node_modules directories along the way (the root's and
 * each ancestor directory's that has one).
 */
export function writeSnapshotTree(files: Record<string, string>): string {
  const root = tempRoot("polly-program-tree-");
  writeFiles(root, files);
  const dirs = new Set<string>([""]);
  for (const file of Object.keys(files)) {
    for (let dir = path.dirname(file); dir !== "."; dir = path.dirname(dir)) dirs.add(dir);
  }
  for (const dir of dirs) {
    const real = path.join(REPO_ROOT, dir, "node_modules");
    if (fs.existsSync(real)) linkNodeModules(real, path.join(root, dir, "node_modules"), root);
  }
  return root;
}

/** Every corpus the tests run on, written out, with the path normaliser for its answers. */
export interface Corpora {
  edge: { tsconfig: string; root: string };
  tree: string;
  tsconfig(name: CorpusName): string;
  /**
   * A path as the oracle stores it: `<edge>/...` or tree-relative for corpus
   * files, `<nm>/...` (after the last node_modules) for package files, so a
   * new temp dir or a package-store layout does not change the answer.
   */
  rel(file: string): string;
  /** `rel` applied to every path quoted in a type text (`import("/abs/node_modules/x")`). */
  relText(text: string): string;
  remove(): void;
}

export function writeCorpora(snapshot: Record<string, string> = readSnapshot()): Corpora {
  const edge = writeEdgeProject();
  const tree = writeSnapshotTree(snapshot);
  const NM = "/node_modules/";
  const rel = (file: string): string => {
    const nm = file.lastIndexOf(NM);
    if (nm >= 0) return `<nm>/${file.slice(nm + NM.length)}`;
    if (file === edge.root || file.startsWith(`${edge.root}/`)) {
      return `<edge>${file.slice(edge.root.length)}`;
    }
    if (file.startsWith(`${tree}/`)) return file.slice(tree.length + 1);
    return file;
  };
  return {
    edge,
    tree,
    tsconfig: (name) =>
      name === "edge" ? edge.tsconfig : path.join(tree, SNAPSHOT_TSCONFIGS[name]),
    rel,
    relText: (text) => text.replace(/"(\/[^"]+)"/g, (_, file: string) => `"${rel(file)}"`),
    remove() {
      fs.rmSync(edge.root, { recursive: true, force: true });
      fs.rmSync(tree, { recursive: true, force: true });
    },
  };
}

export function readOracle<T>(name: string): T {
  const parsed: unknown = JSON.parse(fs.readFileSync(path.join(ORACLE_DIR, name), "utf8"));
  // cast: generic deserialisation boundary; the file is written by oracle/record.ts.
  return parsed as T;
}

export const sha256 = (text: string): string =>
  createHash("sha256").update(text).digest("hex").slice(0, 16);

/** Collects every difference so a failing test prints all of them, not just the first. */
export class Mismatches {
  readonly rows: string[] = [];

  check(where: string, what: string, expected: unknown, actual: unknown): void {
    const a = JSON.stringify(expected);
    const b = JSON.stringify(actual);
    if (a !== b) this.rows.push(`${where} ${what}: ${a} vs ${b}`);
  }

  /** The first rows, for a readable `toEqual([])` failure. */
  head(limit = 20): string[] {
    return this.rows.slice(0, limit);
  }
}
