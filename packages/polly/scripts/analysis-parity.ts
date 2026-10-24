#!/usr/bin/env bun
/**
 * Parity gate for the static-analysis extractors (ts-morph today).
 *
 * Captures the full output of every ts-morph-based extractor over a fixed
 * corpus and compares it, byte for byte, against recorded goldens. It exists
 * so a port of the extractors (ts-morph → typescript-7/async) can be shown to
 * reproduce today's output exactly.
 *
 * Extractors, per project (cwd = the project directory, as a CLI user runs):
 *   verify.analyzeCodebase       `polly verify` / `polly verify --setup` path:
 *                                the CLI's tsconfig + state-file lookup, then
 *                                analyzeCodebase (TypeExtractor → HandlerExtractor
 *                                → RelationshipExtractor).
 *   analysis.extractHandlers     HandlerExtractor.extractHandlers() direct; exposes
 *                                `messageTypes` and `warnings`, which
 *                                analyzeCodebase drops.
 *   visualize.analyzeArchitecture `polly visualize` path: the CLI's tsconfig +
 *                                project-root lookup, then analyzeArchitecture
 *                                (handlers with workspace context overrides,
 *                                contexts, flows, integrations).
 *   adapters.detectAdapter       AdapterDetector; the suggested adapter instance
 *                                is recorded as {class, name, config}.
 *   adapters.selectAdapter       registry: detectProjectConfig(root).type →
 *                                selectAdapter(...).extractModel().
 *   adapters.web-extension       WebExtensionAdapter, default config, extractModel().
 *   adapters.websocket           WebSocketAdapter, default config, extractModel().
 *   adapters.event-bus           EventBusAdapter, default config, extractModel().
 *                                Every extractor shares one typescript-7
 *                                AnalysisSession per worker (closed when the worker
 *                                ends). analyzeCodebase's type queries run on an
 *                                isolated program of it (union order follows checker
 *                                history); analyzeArchitecture opens the shared
 *                                program, so it carries the load time the adapters
 *                                then reuse.
 *
 * Every extractor records its return value (or the error it throws, as
 * name + message) and the console output it wrote. Each project runs in its
 * own subprocess, so no ts-morph or module state crosses projects.
 *
 * Encoding: insertion order is kept (no sorting; recording twice is identical).
 * Map, Set, RegExp, undefined, non-finite numbers and class instances are
 * tagged so they stay distinguishable from plain JSON. Absolute paths are
 * rewritten to `<project>` (the project directory), `<polly>` (this monorepo)
 * and `<home>`; nothing else is normalised.
 *
 * Goldens: in-repo projects → scripts/analysis-parity/golden/ (committed);
 * external consumers (fairfox, lingua, eal) → reports/analysis-parity/golden/
 * (gitignored; their code is not ours to commit). An external project whose
 * directory is absent is skipped with a notice.
 *
 * Machine state the goldens depend on: workspaces that import @fairfox/polly
 * resolve it to packages/polly/dist, and IntegrationAnalyzer scans those .d.ts
 * files, so a rebuilt dist (build:lib) can change a golden on its own.
 *
 * Usage (from anywhere):
 *   bun packages/polly/scripts/analysis-parity.ts            compare; exit 1 on any difference
 *   bun packages/polly/scripts/analysis-parity.ts --record   (re)write the goldens
 *     --only <substr>[,<substr>]  restrict to projects whose id contains a substring
 *     --no-external               skip the external consumers
 * Timings (ms per project per extractor) are printed and written to
 * reports/analysis-parity/timings.json; they are never part of a golden.
 */

import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { analyzeArchitecture } from "../tools/analysis/src/extract/architecture";
import { HandlerExtractor } from "../tools/analysis/src/extract/handlers";
import { detectProjectConfig } from "../tools/analysis/src/extract/project-detector";
import { AnalysisSession } from "../tools/analysis/src/program";
import { detectAdapter } from "../tools/verify/src/adapters/detection";
import { EventBusAdapter } from "../tools/verify/src/adapters/event-bus";
import { selectAdapter } from "../tools/verify/src/adapters/registry";
import { WebExtensionAdapter } from "../tools/verify/src/adapters/web-extension";
import { WebSocketAdapter } from "../tools/verify/src/adapters/websocket";
import { analyzeCodebase } from "../tools/verify/src/extract/types";

const PKG = resolve(import.meta.dir, "..");
const ROOT = resolve(PKG, "../..");
const PROJECTS_DIR = resolve(ROOT, "..");
const GOLDEN_INTERNAL = join(PKG, "scripts/analysis-parity/golden");
const GOLDEN_EXTERNAL = join(ROOT, "reports/analysis-parity/golden");
const REPORT_DIR = join(ROOT, "reports/analysis-parity");
const HOME = homedir();

interface Project {
  /** Stable id; also the golden's relative path. */
  id: string;
  dir: string;
  external: boolean;
}

const INTERNAL_DIRS = [
  "examples/blob-share/client",
  "examples/blob-share/server",
  "examples/elysia-todo-app/client",
  "examples/elysia-todo-app/server",
  "examples/full-featured",
  "examples/mesh-large-initial-sync",
  "examples/mesh-large-initial-sync-turn",
  "examples/mesh-recovery-pair",
  "examples/minimal",
  "examples/showcase",
  "examples/team-task-manager/client",
  "examples/team-task-manager/server",
  "examples/todo-list",
  "examples/webrtc-p2p-chat/client",
  "examples/webrtc-p2p-chat/server",
  "packages/polly/tools/verify/test-projects/capability-guard",
  "packages/polly/tools/verify/test-projects/coverage-offsurface",
  "packages/polly/tools/verify/test-projects/coverage-strict",
  "packages/polly/tools/verify/test-projects/electron",
  "packages/polly/tools/verify/test-projects/mesh-seed-guard",
  "packages/polly/tools/verify/test-projects/naming-collision",
  "packages/polly/tools/verify/test-projects/pwa",
  "packages/polly/tools/verify/test-projects/websocket-server",
  // Harness-owned: reaches the type conversion the examples barely touch.
  "packages/polly/scripts/analysis-parity/fixtures/types-corpus",
  // Harness-owned: UI components, sender annotations, integrations, relationships.
  "packages/polly/scripts/analysis-parity/fixtures/architecture-corpus",
];

/** Read-only consumers outside this repo, relative to ~/projects. */
const EXTERNAL_DIRS = ["fairfox/packages/server", "lingua", "lingua/packages/api", "eal"];

const PROJECTS: Project[] = [
  ...INTERNAL_DIRS.map((d) => ({ id: d, dir: join(ROOT, d), external: false })),
  ...EXTERNAL_DIRS.map((d) => ({
    id: `external/${d}`,
    dir: join(PROJECTS_DIR, d),
    external: true,
  })),
];

const EXTRACTORS = [
  "verify.analyzeCodebase",
  "analysis.extractHandlers",
  "visualize.analyzeArchitecture",
  "adapters.detectAdapter",
  "adapters.selectAdapter",
  "adapters.web-extension",
  "adapters.websocket",
  "adapters.event-bus",
] as const;
type ExtractorName = (typeof EXTRACTORS)[number];

interface ExtractorRecord {
  result?: unknown;
  error?: { name: string; message: string };
  logs: string[];
}

interface WorkerOutput {
  project: string;
  extractors: Record<string, ExtractorRecord>;
  timings: Record<string, number>;
}

// ── encoding ───────────────────────────────────────────────────────────────

/** Rewrite absolute paths in a string: longest prefix first. */
function makeRelativiser(projectDir: string): (s: string) => string {
  const pairs: Array<[string, string]> = [
    [projectDir, "<project>"],
    [ROOT, "<polly>"],
    [HOME, "<home>"],
  ];
  return (s) => {
    let out = s;
    for (const [abs, token] of pairs) out = out.split(abs).join(token);
    return out;
  };
}

function className(value: object): string {
  const proto: unknown = Object.getPrototypeOf(value);
  if (proto === null || proto === Object.prototype) return "Object";
  const ctor: unknown = isObject(proto) ? Reflect.get(proto, "constructor") : undefined;
  return typeof ctor === "function" && ctor.name ? ctor.name : "<anonymous>";
}

function isObject(value: unknown): value is object {
  return typeof value === "object" && value !== null;
}

/**
 * Turn an extractor's output into plain JSON without losing anything JSON
 * would silently drop or merge. Throws on cycles and on functions, so a new
 * kind of value forces a decision here instead of disappearing.
 */
function encode(
  value: unknown,
  rel: (s: string) => string,
  seen: Set<object> = new Set()
): unknown {
  if (value === undefined) return { $type: "undefined" };
  if (value === null || typeof value === "boolean") return value;
  if (typeof value === "string") return rel(value);
  if (typeof value === "number") return encodeNumber(value);
  if (typeof value === "bigint") return { $type: "bigint", value: value.toString() };
  if (typeof value === "symbol" || typeof value === "function") {
    throw new Error(`cannot encode a ${typeof value}: ${String(value)}`);
  }
  if (seen.has(value)) throw new Error("cannot encode a cycle");
  seen.add(value);
  try {
    return encodeObject(value, (v) => encode(v, rel, seen), rel);
  } finally {
    seen.delete(value);
  }
}

function encodeNumber(value: number): unknown {
  if (!Number.isFinite(value)) return { $type: "number", value: String(value) };
  return Object.is(value, -0) ? { $type: "number", value: "-0" } : value;
}

function encodeObject(
  value: object,
  inner: (v: unknown) => unknown,
  rel: (s: string) => string
): unknown {
  if (Array.isArray(value)) return value.map(inner);
  if (value instanceof Map) {
    return { $type: "Map", entries: [...value.entries()].map(([k, v]) => [inner(k), inner(v)]) };
  }
  if (value instanceof Set) return { $type: "Set", values: [...value].map(inner) };
  if (value instanceof RegExp) return { $type: "RegExp", source: value.source, flags: value.flags };
  const name = className(value);
  if (name !== "Object") {
    throw new Error(`cannot encode a ${name} instance; describe it explicitly in the extractor`);
  }
  const fields: Record<string, unknown> = {};
  for (const key of Object.keys(value)) fields[rel(key)] = inner(Reflect.get(value, key));
  return fields;
}

/** An adapter instance as data: its class, name and config. */
function describeAdapter(adapter: unknown): unknown {
  if (!isObject(adapter)) return adapter;
  return {
    class: className(adapter),
    name: Reflect.get(adapter, "name"),
    config: Reflect.get(adapter, "config"),
  };
}

// ── worker: one project, every extractor ───────────────────────────────────

/** `polly verify`'s tsconfig lookup (tools/verify/src/cli.ts findTsConfig). */
function verifyTsConfig(cwd: string): string | null {
  const locations = [join(cwd, "tsconfig.json"), join(cwd, "packages", "web-ext", "tsconfig.json")];
  return locations.find((loc) => existsSync(loc)) ?? null;
}

/** `polly verify`'s state-file lookup (tools/verify/src/cli.ts findStateFile). */
function verifyStateFile(cwd: string): string | undefined {
  const locations = [
    join(cwd, "types", "state.ts"),
    join(cwd, "src", "types", "state.ts"),
    join(cwd, "packages", "web-ext", "src", "shared", "state", "app-state.ts"),
  ];
  return locations.find((loc) => existsSync(loc));
}

/** `polly visualize`'s tsconfig lookup (tools/visualize/src/cli.ts findTsConfig). */
function visualizeTsConfig(cwd: string): string | null {
  const locations = [join(cwd, "tsconfig.json"), join(cwd, "..", "tsconfig.json")];
  return locations.find((loc) => existsSync(loc)) ?? null;
}

/** `polly visualize`'s project-root lookup (tools/visualize/src/cli.ts findProjectRoot). */
function visualizeProjectRoot(cwd: string): string | null {
  const locations = [cwd, join(cwd, "..")];
  return (
    locations.find(
      (loc) =>
        existsSync(join(loc, "manifest.json")) ||
        existsSync(join(loc, "package.json")) ||
        existsSync(join(loc, "tsconfig.json"))
    ) ?? null
  );
}

function required<T>(value: T | null, what: string): T {
  if (value === null) throw new Error(`no ${what} found (the CLI would exit 1 here)`);
  return value;
}

async function runExtractor(
  name: ExtractorName,
  cwd: string,
  session: AnalysisSession
): Promise<unknown> {
  switch (name) {
    case "verify.analyzeCodebase": {
      return await analyzeCodebase({
        tsConfigPath: required(verifyTsConfig(cwd), "tsconfig"),
        stateFilePath: verifyStateFile(cwd),
        session,
      });
    }
    case "analysis.extractHandlers": {
      return new HandlerExtractor(required(verifyTsConfig(cwd), "tsconfig")).extractHandlers();
    }
    case "visualize.analyzeArchitecture": {
      return await analyzeArchitecture({
        tsConfigPath: required(visualizeTsConfig(cwd), "tsconfig"),
        projectRoot: required(visualizeProjectRoot(cwd), "project root"),
        session,
      });
    }
    case "adapters.detectAdapter": {
      const result = await detectAdapter(required(verifyTsConfig(cwd), "tsconfig"), session);
      return { ...result, suggestedAdapter: describeAdapter(result.suggestedAdapter) };
    }
    case "adapters.selectAdapter": {
      const projectType = detectProjectConfig(cwd).type;
      const tsConfigPath = required(verifyTsConfig(cwd), "tsconfig");
      const adapter = await selectAdapter(projectType, tsConfigPath, session);
      const model = await adapter.extractModel(session);
      return { projectType, adapter: describeAdapter(adapter), model };
    }
    case "adapters.web-extension": {
      const tsConfigPath = required(verifyTsConfig(cwd), "tsconfig");
      return await new WebExtensionAdapter({ tsConfigPath }).extractModel(session);
    }
    case "adapters.websocket": {
      const tsConfigPath = required(verifyTsConfig(cwd), "tsconfig");
      return await new WebSocketAdapter({ tsConfigPath }).extractModel(session);
    }
    case "adapters.event-bus": {
      const tsConfigPath = required(verifyTsConfig(cwd), "tsconfig");
      return await new EventBusAdapter({ tsConfigPath }).extractModel(session);
    }
  }
}

/** Run `fn` with console output captured as lines instead of printed. */
async function captureConsole<T>(fn: () => Promise<T>): Promise<{ value: T; logs: string[] }> {
  const logs: string[] = [];
  const methods = ["log", "info", "warn", "error", "debug"];
  // Reflect, not member access: the extractors' own console calls are the
  // output being captured, and this is the one place that swaps them out.
  const saved = methods.map((m) => Reflect.get(console, m));
  for (const m of methods) {
    Reflect.set(console, m, (...args: unknown[]) => {
      logs.push(`${m}: ${args.map((a) => (typeof a === "string" ? a : Bun.inspect(a))).join(" ")}`);
    });
  }
  try {
    return { value: await fn(), logs };
  } finally {
    methods.forEach((m, i) => {
      Reflect.set(console, m, saved[i]);
    });
  }
}

async function worker(projectId: string, outFile: string): Promise<void> {
  const project = PROJECTS.find((p) => p.id === projectId);
  if (!project) throw new Error(`unknown project ${projectId}`);
  const cwd = project.dir;
  process.chdir(cwd);
  const rel = makeRelativiser(cwd);
  const out: WorkerOutput = { project: projectId, extractors: {}, timings: {} };
  await using session = new AnalysisSession({ cwd });

  for (const name of EXTRACTORS) {
    const started = performance.now();
    const logs: string[] = [];
    let record: ExtractorRecord;
    try {
      const captured = await captureConsole(() => runExtractor(name, cwd, session));
      logs.push(...captured.logs);
      record = { result: encode(captured.value, rel), logs: [] };
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      record = { error: { name: err.name, message: rel(err.message) }, logs: [] };
    }
    out.timings[name] = Math.round(performance.now() - started);
    record.logs = logs.map(rel);
    out.extractors[name] = record;
  }
  writeFileSync(outFile, JSON.stringify(out));
}

// ── driver ─────────────────────────────────────────────────────────────────

function goldenPath(project: Project): string {
  return join(project.external ? GOLDEN_EXTERNAL : GOLDEN_INTERNAL, `${project.id}.json`);
}

function serialise(extractors: Record<string, ExtractorRecord>): string {
  return `${JSON.stringify(extractors, null, 2)}\n`;
}

async function runProject(project: Project): Promise<WorkerOutput> {
  mkdirSync(REPORT_DIR, { recursive: true });
  const outFile = join(REPORT_DIR, `worker-${project.id.replaceAll("/", "__")}.json`);
  const proc = Bun.spawn(["bun", import.meta.path, "--worker", project.id, outFile], {
    cwd: project.dir,
    stdout: "inherit",
    stderr: "inherit",
  });
  const code = await proc.exited;
  if (code !== 0) throw new Error(`worker for ${project.id} exited ${code}`);
  const parsed: unknown = JSON.parse(readFileSync(outFile, "utf8"));
  if (!isWorkerOutput(parsed)) throw new Error(`worker for ${project.id} wrote malformed output`);
  return parsed;
}

function isWorkerOutput(value: unknown): value is WorkerOutput {
  return (
    isObject(value) &&
    typeof Reflect.get(value, "project") === "string" &&
    isObject(Reflect.get(value, "extractors")) &&
    isObject(Reflect.get(value, "timings"))
  );
}

function short(value: unknown): string {
  const s = value === undefined ? "<absent>" : JSON.stringify(value);
  return s.length > 160 ? `${s.slice(0, 157)}...` : s;
}

/** The first `limit` differing paths between two decoded JSON values. */
function differences(
  expected: unknown,
  actual: unknown,
  path: string,
  out: string[],
  limit: number
): void {
  if (out.length >= limit) return;
  if (Array.isArray(expected) && Array.isArray(actual)) {
    if (expected.length !== actual.length) {
      out.push(`${path}: length ${expected.length} → ${actual.length}`);
    }
    for (let i = 0; i < Math.max(expected.length, actual.length); i++) {
      differences(expected[i], actual[i], `${path}[${i}]`, out, limit);
    }
    return;
  }
  if (
    isObject(expected) &&
    isObject(actual) &&
    !Array.isArray(expected) &&
    !Array.isArray(actual)
  ) {
    const ek = Object.keys(expected);
    const ak = Object.keys(actual);
    if (ek.join("\0") !== ak.join("\0") && new Set(ek).size === new Set([...ek, ...ak]).size) {
      out.push(`${path}: key order ${short(ek)} → ${short(ak)}`);
    }
    for (const key of [...new Set([...ek, ...ak])]) {
      differences(
        Reflect.get(expected, key),
        Reflect.get(actual, key),
        `${path}.${key}`,
        out,
        limit
      );
    }
    return;
  }
  if (JSON.stringify(expected) !== JSON.stringify(actual)) {
    out.push(`${path}: ${short(expected)} → ${short(actual)}`);
  }
}

function pad(s: string, n: number): string {
  return s.length >= n ? s : s + " ".repeat(n - s.length);
}

type Outcome = "recorded" | "same" | "differs" | "skipped";

/** Run one project and record or compare its golden. */
async function checkProject(
  project: Project,
  record: boolean,
  timings: Record<string, Record<string, number>>
): Promise<Outcome> {
  if (!existsSync(project.dir)) {
    if (!project.external)
      throw new Error(`corpus project ${project.id} is missing at ${project.dir}`);
    console.log(`– skip ${project.id}: ${project.dir} is absent`);
    return "skipped";
  }
  const started = performance.now();
  const output = await runProject(project);
  timings[project.id] = output.timings;
  const actual = serialise(output.extractors);
  const golden = goldenPath(project);
  const errored = EXTRACTORS.filter((e) => output.extractors[e]?.error).length;
  const took = `${Math.round(performance.now() - started)} ms`;
  const note = errored > 0 ? `, ${errored} extractor(s) recorded as error` : "";

  if (record) {
    mkdirSync(dirname(golden), { recursive: true });
    writeFileSync(golden, actual);
    console.log(`✓ recorded ${project.id} (${took}${note})`);
    return "recorded";
  }
  if (!existsSync(golden)) {
    console.log(`✗ ${project.id}: no golden at ${golden} (run with --record)`);
    return "differs";
  }
  const expectedText = readFileSync(golden, "utf8");
  if (expectedText === actual) {
    console.log(`✓ ${project.id} (${took}${note})`);
    return "same";
  }
  console.log(`✗ ${project.id} differs from ${golden}`);
  printDifferences(JSON.parse(expectedText), output.extractors);
  if (expectedText.includes("<polly>/packages/polly/dist/")) {
    console.log(
      "    note: this golden reads packages/polly/dist (.d.ts via node_modules/@fairfox/polly);\n" +
        "    a dist rebuilt since recording changes it without any extractor change"
    );
  }
  return "differs";
}

function printDifferences(expected: unknown, actual: Record<string, ExtractorRecord>): void {
  for (const name of EXTRACTORS) {
    const e = isObject(expected) ? Reflect.get(expected, name) : undefined;
    const a = actual[name];
    if (JSON.stringify(e) === JSON.stringify(a)) continue;
    const diffs: string[] = [];
    differences(e, a, name, diffs, 12);
    console.log(`    extractor ${name}:`);
    for (const d of diffs) console.log(`      ${d}`);
  }
}

/** Print the project × extractor timing table and keep it for later runs to compare. */
function printTimings(timings: Record<string, Record<string, number>>): void {
  const ids = Object.keys(timings);
  if (ids.length === 0) return;
  const width = Math.max(...ids.map((i) => i.length));
  const cols = EXTRACTORS.map((e) => e.replace(/^\w+\./, ""));
  console.log(`\n${pad("ms", width)}  ${cols.map((c) => pad(c, 10)).join(" ")}`);
  for (const id of ids) {
    const row = EXTRACTORS.map((e) => pad(String(timings[id]?.[e] ?? "-"), 10));
    console.log(`${pad(id, width)}  ${row.join(" ")}`);
  }
  mkdirSync(REPORT_DIR, { recursive: true });
  writeFileSync(join(REPORT_DIR, "timings.json"), `${JSON.stringify(timings, null, 2)}\n`);
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const workerAt = argv.indexOf("--worker");
  if (workerAt >= 0) {
    const id = argv[workerAt + 1];
    const out = argv[workerAt + 2];
    if (!id || !out) throw new Error("--worker <project> <outFile>");
    await worker(id, out);
    return;
  }

  const record = argv.includes("--record");
  const noExternal = argv.includes("--no-external");
  const onlyArg = argv.includes("--only") ? argv[argv.indexOf("--only") + 1] : undefined;
  const only = onlyArg ? onlyArg.split(",") : null;
  const selected = PROJECTS.filter(
    (p) => !(noExternal && p.external) && (!only || only.some((o) => p.id.includes(o)))
  );

  const timings: Record<string, Record<string, number>> = {};
  const outcomes = new Map<string, Outcome>();
  for (const project of selected) {
    outcomes.set(project.id, await checkProject(project, record, timings));
  }
  printTimings(timings);

  if (record) return;
  const failures = [...outcomes].filter(([, o]) => o === "differs").map(([id]) => id);
  if (failures.length > 0) {
    console.log(
      `\n✗ analysis parity: ${failures.length} project(s) differ: ${failures.join(", ")}`
    );
    process.exit(1);
  }
  const same = [...outcomes.values()].filter((o) => o === "same").length;
  console.log(`\n✓ analysis parity: ${same} project(s) identical to their goldens`);
}

await main();
