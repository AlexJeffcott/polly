/**
 * Static test selection: which test files can reach a target?
 *
 * Starting from every test file, follow resolved imports (Bun's own resolver,
 * so tsconfig `paths` such as `@/` work) through project source, never into
 * node_modules. A test covers a target when the target is in its import
 * closure. Reach that no import names — `mock.module`, a computed `import()`,
 * a global set by another file — is invisible here; a dynamic coverage pass is
 * the planned answer to that.
 */
import { realpathSync } from "node:fs";
import { dirname, extname } from "node:path";
import { Glob } from "bun";

const SOURCE_EXTENSIONS = new Set([".ts", ".tsx", ".js", ".jsx", ".mts", ".cts", ".mjs", ".cjs"]);

export interface ImportGraph {
  testFiles: string[];
  /** file → files it imports (absolute, symlink-resolved). */
  imports: Map<string, string[]>;
}

function loaderFor(file: string): "ts" | "tsx" | "js" | "jsx" {
  const ext = extname(file);
  if (ext === ".tsx") return "tsx";
  if (ext === ".jsx") return "jsx";
  if (ext === ".ts" || ext === ".mts" || ext === ".cts") return "ts";
  return "js";
}

function real(path: string): string {
  try {
    return realpathSync(path);
  } catch {
    return path;
  }
}

export async function findTestFiles(cwd: string, include: string[]): Promise<string[]> {
  const found = new Set<string>();
  for (const pattern of include) {
    for await (const f of new Glob(pattern).scan({ cwd, absolute: true, onlyFiles: true })) {
      if (!f.includes("/node_modules/")) found.add(real(f));
    }
  }
  return [...found].sort();
}

const transpilers = new Map<string, Bun.Transpiler>();
function scan(file: string, text: string): string[] {
  const loader = loaderFor(file);
  let t = transpilers.get(loader);
  if (!t) {
    t = new Bun.Transpiler({ loader });
    transpilers.set(loader, t);
  }
  try {
    return t.scanImports(text).map((i) => i.path);
  } catch {
    return [];
  }
}

/** Project source files `file` imports at runtime, resolved the way Bun resolves them. */
function resolveImports(file: string, text: string): string[] {
  const out: string[] = [];
  for (const spec of scan(file, text)) {
    if (spec.startsWith("bun:") || spec.startsWith("node:")) continue;
    let resolved: string;
    try {
      resolved = real(Bun.resolveSync(spec, dirname(file)));
    } catch {
      continue;
    }
    if (!resolved.includes("/node_modules/") && SOURCE_EXTENSIONS.has(extname(resolved))) {
      out.push(resolved);
    }
  }
  return out;
}

export async function buildImportGraph(testFiles: string[]): Promise<ImportGraph> {
  const imports = new Map<string, string[]>();
  const queue = [...testFiles];
  for (let file = queue.pop(); file !== undefined; file = queue.pop()) {
    if (imports.has(file)) continue;
    const out = resolveImports(file, await Bun.file(file).text());
    imports.set(file, out);
    queue.push(...out.filter((f) => !imports.has(f)));
  }
  return { testFiles, imports };
}

function importersOf(graph: ImportGraph): Map<string, string[]> {
  const importers = new Map<string, string[]>();
  for (const [from, tos] of graph.imports) {
    for (const to of tos) importers.set(to, [...(importers.get(to) ?? []), from]);
  }
  return importers;
}

/** Test files whose import closure contains `target`, sorted. */
export function coveringTests(graph: ImportGraph, target: string): string[] {
  const importers = importersOf(graph);
  const wanted = real(target);
  const seen = new Set([wanted]);
  const stack = [wanted];
  for (let f = stack.pop(); f !== undefined; f = stack.pop()) {
    const fresh = (importers.get(f) ?? []).filter((p) => !seen.has(p));
    for (const p of fresh) seen.add(p);
    stack.push(...fresh);
  }
  const tests = new Set(graph.testFiles);
  return [...seen].filter((f) => tests.has(f)).sort();
}
