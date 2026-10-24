// Shared corpora for the program-module tests: each is loaded twice, once by
// ts-morph (the reference answer) and once through an AnalysisSession.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

export const POLLY_ROOT = path.resolve(import.meta.dir, "../../../../..");
export const REPO_ROOT = path.resolve(POLLY_ROOT, "../..");
export const TYPES_CORPUS = path.join(
  POLLY_ROOT,
  "scripts/analysis-parity/fixtures/types-corpus/tsconfig.json"
);
export const FULL_FEATURED = path.join(REPO_ROOT, "examples/full-featured/tsconfig.json");
export const TODO_LIST = path.join(REPO_ROOT, "examples/todo-list/tsconfig.json");

const LS = " ";

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

/** Write the edge-case project into a fresh temp dir (symlinks resolved) and return its tsconfig. */
export function writeEdgeProject(): { tsconfig: string; root: string } {
  const root = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), "polly-program-edge-"));
  for (const [file, text] of Object.entries(EDGE_FILES)) {
    const target = path.join(root, file);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, text);
  }
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
