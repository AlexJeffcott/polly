#!/usr/bin/env bun
/**
 * Parity gate: the Bun-native engine against Stryker, on four targets.
 *
 *   validation.ts            pure logic
 *   mesh-network-adapter.ts  the spike's target; async, event-driven
 *   crdt-state.ts            automerge-backed state
 *   ActionInput.tsx          polly-ui; its covering tests need the CSS-module
 *                            shim (tests/setup.ts) and pull in Modal, whose
 *                            preact/compat import rebinds onBlur process-wide
 *
 * Both tools run in fast mode (bail at the first failing test) with the same
 * concurrency, one after the other. Mutants match on
 * (file, mutatorName, line, replacement); replacements are normalised first,
 * because the engine's are source text and Stryker's are Babel output.
 *
 * Pass criteria:
 *   1. ≥ 95 % of Stryker's mutants matched, for the mutators both tools have.
 *   2. No matched mutant that the engine calls Survived and Stryker Killed,
 *      once each candidate is re-run against the full unit suite (a candidate
 *      the full suite does not kill is not a kill the engine lost).
 *   3. Scores within 2 points, over the mutators both tools have, without the
 *      verify-callsite mutants the engine marks Ignored.
 *   4. The engine is ≥ 10× faster in wall time.
 *
 * Writes scripts/mutate-parity.results.md; raw reports go to
 * reports/mutate-parity/ (gitignored).
 *
 * Usage (from anywhere; runs at the monorepo root):
 *   bun packages/polly/scripts/mutate-parity.ts
 *     --reuse-stryker   use reports/mutate-parity/stryker.json from a past run
 *     --reuse-engine    use reports/mutate-parity/engine.json from a past run
 *     --full-run        also run the engine alone on every polly.mutate.ts target
 * Exit 0 when all four criteria pass.
 */

import { mkdirSync, realpathSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { isRecord } from "../src/shared/lib/guards";

const PKG = resolve(import.meta.dir, "..");
const ROOT = resolve(PKG, "../..");
const OUT = join(ROOT, "reports/mutate-parity");
const RESULTS = join(PKG, "scripts/mutate-parity.results.md");
const CLI = join(PKG, "cli/polly.ts");
const PRELOAD = join(PKG, "tools/mutate/src/engine/preload.ts");
const SETUP = "./packages/polly/tests/setup.ts";
const TEST_GLOB = "packages/polly/tests/unit/**/*.test.ts";
const CONCURRENCY = 6;

const TARGETS = [
  "packages/polly/src/shared/lib/validation.ts",
  "packages/polly/src/shared/lib/mesh-network-adapter.ts",
  "packages/polly/src/shared/lib/crdt-state.ts",
  "packages/polly/src/polly-ui/ActionInput.tsx",
];

interface ReportMutant {
  file: string;
  id: string;
  mutatorName: string;
  replacement: string;
  status: string;
  start: { line: number; column: number };
  end: { line: number; column: number };
}

interface ParsedReport {
  mutants: ReportMutant[];
  sources: Map<string, string>;
}

// ── running ────────────────────────────────────────────────────────────────

async function timed(argv: string[], env: Record<string, string> = {}): Promise<number> {
  const started = performance.now();
  const proc = Bun.spawn(argv, {
    cwd: ROOT,
    stdout: "inherit",
    stderr: "inherit",
    env: { ...process.env, ...env },
  });
  const code = await proc.exited;
  if (code !== 0) throw new Error(`${argv.join(" ")} exited ${code}`);
  return performance.now() - started;
}

async function runEngine(files: string[] | null, report: string): Promise<number> {
  return await timed([
    "bun",
    CLI,
    "mutate",
    "run",
    "--mode",
    "fast",
    "--no-cache",
    "--concurrency",
    String(CONCURRENCY),
    "--report",
    report,
    ...(files ? ["--files", files.join(",")] : []),
  ]);
}

/** Stryker on the targets, with the root stryker.conf.json's runner setup but bail on. */
async function runStryker(report: string): Promise<number> {
  const config = join(OUT, "stryker.parity.json");
  writeFileSync(
    config,
    JSON.stringify(
      {
        packageManager: "npm",
        testRunner: "bun",
        plugins: ["stryker-mutator-bun-runner"],
        bun: { testFiles: [TEST_GLOB], nodeArgs: ["--preload", SETUP], timeout: 30000 },
        coverageAnalysis: "all",
        disableBail: false,
        checkers: [],
        reporters: ["json", "progress"],
        jsonReporter: { fileName: report },
        mutate: TARGETS,
        ignorePatterns: [
          "**/node_modules/**",
          "**/dist/**",
          "**/.git/**",
          "**/.stryker-tmp/**",
          "**/reports/**",
        ],
        timeoutMS: 90000,
        concurrency: CONCURRENCY,
      },
      null,
      2
    )
  );
  return await timed(["bunx", "stryker", "run", config]);
}

// ── reading reports ────────────────────────────────────────────────────────

function position(value: unknown): { line: number; column: number } {
  if (isRecord(value) && typeof value["line"] === "number" && typeof value["column"] === "number")
    return { line: value["line"], column: value["column"] };
  throw new Error(`malformed location: ${JSON.stringify(value)}`);
}

function parseMutant(file: string, m: unknown): ReportMutant | null {
  if (!isRecord(m) || !isRecord(m["location"])) return null;
  return {
    file,
    id: String(m["id"]),
    mutatorName: String(m["mutatorName"]),
    replacement: typeof m["replacement"] === "string" ? m["replacement"] : "",
    status: String(m["status"]),
    start: position(m["location"]["start"]),
    end: position(m["location"]["end"]),
  };
}

async function readReport(path: string): Promise<ParsedReport> {
  const json: unknown = await Bun.file(path).json();
  if (!isRecord(json) || !isRecord(json["files"])) throw new Error(`${path}: no files`);
  const mutants: ReportMutant[] = [];
  const sources = new Map<string, string>();
  for (const [file, entry] of Object.entries(json["files"])) {
    if (!isRecord(entry) || !Array.isArray(entry["mutants"])) continue;
    if (typeof entry["source"] === "string") sources.set(file, entry["source"]);
    for (const m of entry["mutants"]) {
      const parsed = parseMutant(file, m);
      if (parsed) mutants.push(parsed);
    }
  }
  return { mutants, sources };
}

// ── matching ───────────────────────────────────────────────────────────────

/** Source text vs Babel output: drop whitespace, parens, semicolons; one quote style. */
export function normalise(text: string): string {
  return text.replace(/[\s();]/g, "").replace(/['`]/g, '"');
}

/**
 * The two tools mark the same edit with different spans: the engine replaces
 * the smallest span (`!==` alone, or `` to drop a `!`), Stryker the whole node
 * (`next !== currentHandle`). The mutated file is the same, so the key hashes
 * that, normalised.
 */
function key(m: ReportMutant, sources: Map<string, string>): string {
  const src = sources.get(m.file) ?? "";
  const mutated =
    src.slice(0, offset(src, m.start)) + m.replacement + src.slice(offset(src, m.end));
  return `${m.file}|${m.mutatorName}|${m.start.line}|${Bun.hash(normalise(mutated))}`;
}

interface Match {
  engine: ReportMutant;
  stryker: ReportMutant;
}

/** Multiset match on the plan's key; leftovers are reported, never paired loosely. */
function match(
  engine: ReportMutant[],
  engineSources: Map<string, string>,
  stryker: ReportMutant[],
  strykerSources: Map<string, string>
) {
  const pool = new Map<string, ReportMutant[]>();
  for (const e of engine) {
    const k = key(e, engineSources);
    const list = pool.get(k) ?? [];
    list.push(e);
    pool.set(k, list);
  }
  const matched: Match[] = [];
  const strykerOnly: ReportMutant[] = [];
  for (const s of stryker) {
    const e = pool.get(key(s, strykerSources))?.shift();
    if (e) matched.push({ engine: e, stryker: s });
    else strykerOnly.push(s);
  }
  const engineOnly = [...pool.values()].flat();
  return { matched, strykerOnly, engineOnly };
}

function score(statuses: string[]): number | null {
  const detected = statuses.filter((s) => s === "Killed" || s === "Timeout").length;
  const valid = statuses.filter((s) =>
    ["Killed", "Timeout", "Survived", "NoCoverage"].includes(s)
  ).length;
  return valid === 0 ? null : (100 * detected) / valid;
}

// ── full-suite re-check of criterion-2 candidates ──────────────────────────

function offset(src: string, pos: { line: number; column: number }): number {
  let at = 0;
  for (let line = 1; line < pos.line; line++) at = src.indexOf("\n", at) + 1;
  return at + pos.column - 1;
}

async function allTestFiles(): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Bun.Glob(TEST_GLOB).scan({ cwd: ROOT })) out.push(f);
  return out.sort();
}

/** Exit code of the whole unit suite under one engine mutant (0 = it survives the full suite). */
async function fullSuite(m: ReportMutant | null, src: string, files: string[]): Promise<number> {
  const env: Record<string, string> = {};
  if (m) {
    env["POLLY_MUTATE_FILE"] = realpathSync(join(ROOT, m.file));
    env["POLLY_MUTATE_SPAN"] = JSON.stringify({
      start: offset(src, m.start),
      end: offset(src, m.end),
      replacement: m.replacement,
    });
  }
  const proc = Bun.spawn(
    ["bun", "test", "--preload", SETUP, "--preload", PRELOAD, "--bail", ...files],
    { cwd: ROOT, stdout: "ignore", stderr: "ignore", env: { ...process.env, ...env } }
  );
  return await proc.exited;
}

// ── main ───────────────────────────────────────────────────────────────────

const flags = new Set(process.argv.slice(2));
mkdirSync(OUT, { recursive: true });
const engineReport = join(OUT, "engine.json");
const strykerReport = join(OUT, "stryker.json");
const timesPath = join(OUT, "times.json");
const times: Record<string, number> = (await Bun.file(timesPath).exists())
  ? await Bun.file(timesPath).json()
  : {};

if (!flags.has("--reuse-engine")) times["engine"] = await runEngine(TARGETS, engineReport);
if (!flags.has("--reuse-stryker")) times["stryker"] = await runStryker(strykerReport);
if (flags.has("--full-run")) {
  times["engineFull"] = await runEngine(null, join(OUT, "engine-full.json"));
}
writeFileSync(timesPath, JSON.stringify(times, null, 2));

const engine = await readReport(engineReport);
const stryker = await readReport(strykerReport);
const strykerMutators = new Set(stryker.mutants.map((m) => m.mutatorName));
const engineMutators = new Set(engine.mutants.map((m) => m.mutatorName));
const shared = (m: ReportMutant) =>
  strykerMutators.has(m.mutatorName) && engineMutators.has(m.mutatorName);

const { matched, strykerOnly, engineOnly } = match(
  engine.mutants.filter(shared),
  engine.sources,
  stryker.mutants.filter(shared),
  stryker.sources
);
const strykerShared = stryker.mutants.filter(shared).length;
const matchPct = (100 * matched.length) / strykerShared;

// Criterion 2
const candidates = matched.filter(
  (p) => p.engine.status === "Survived" && p.stryker.status === "Killed"
);
const testFiles = await allTestFiles();
const baselineCode = candidates.length > 0 ? await fullSuite(null, "", testFiles) : 0;
const lost: Match[] = [];
const notLost: Match[] = [];
for (const c of candidates) {
  const src = engine.sources.get(c.engine.file) ?? "";
  const code = await fullSuite(c.engine, src, testFiles);
  (code === 0 ? notLost : lost).push(c);
}

// Criterion 3: verify-callsite mutants leave both sides together
const ignoredIds = new Set(
  matched.filter((p) => p.engine.status === "Ignored").map((p) => p.stryker.id)
);
const engineScore = score(
  engine.mutants.filter((m) => shared(m) && m.status !== "Ignored").map((m) => m.status)
);
const strykerScore = score(
  stryker.mutants.filter((m) => shared(m) && !ignoredIds.has(m.id)).map((m) => m.status)
);
const scoreGap =
  engineScore === null || strykerScore === null ? null : Math.abs(engineScore - strykerScore);

const speedup = (times["stryker"] ?? 0) / (times["engine"] ?? 1);

const pass = {
  match: matchPct >= 95,
  lost: lost.length === 0 && baselineCode === 0,
  score: scoreGap !== null && scoreGap <= 2,
  speed: speedup >= 10,
};

// ── results ────────────────────────────────────────────────────────────────

const mark = (ok: boolean) => (ok ? "PASS" : "FAIL");
const pct = (n: number | null) => (n === null ? "n/a" : `${n.toFixed(1)} %`);
const secs = (ms: number | undefined) => (ms === undefined ? "n/a" : `${(ms / 1000).toFixed(1)} s`);
const row = (m: ReportMutant) =>
  `| ${m.file.replace("packages/polly/src/", "")}:${m.start.line}:${m.start.column} | ${m.mutatorName} | \`${m.replacement.replace(/\s+/g, " ").replace(/\|/g, "\\|").slice(0, 60)}\` | ${m.status} |`;

const perFile = TARGETS.map((file) => {
  const e = engine.mutants.filter((m) => m.file === file);
  const s = stryker.mutants.filter((m) => m.file === file);
  return `| ${file.replace("packages/polly/src/", "")} | ${s.length} | ${e.length} | ${matched.filter((p) => p.stryker.file === file).length} | ${pct(score(s.filter((m) => !ignoredIds.has(m.id)).map((m) => m.status)))} | ${pct(score(e.filter((m) => m.status !== "Ignored").map((m) => m.status)))} |`;
});

const statuses = [...new Set(matched.flatMap((p) => [p.engine.status, p.stryker.status]))].sort();
const crossTable = [
  `| Stryker ↓ / engine → | ${statuses.join(" | ")} |`,
  `|---|${statuses.map(() => "---").join("|")}|`,
  ...statuses.map(
    (st) =>
      `| ${st} | ${statuses.map((en) => matched.filter((p) => p.stryker.status === st && p.engine.status === en).length).join(" | ")} |`
  ),
];

const byMutator = (list: ReportMutant[]) => {
  const counts = new Map<string, number>();
  for (const m of list) counts.set(m.mutatorName, (counts.get(m.mutatorName) ?? 0) + 1);
  return [...counts.entries()]
    .sort((a, b) => b[1] - a[1])
    .map(([k, v]) => `${k} ${v}`)
    .join(", ");
};

const lines = [
  "# Mutation engine parity gate",
  "",
  `Generated by \`bun packages/polly/scripts/mutate-parity.ts\` on ${new Date().toISOString().slice(0, 10)}.`,
  `Both tools: fast mode (bail), concurrency ${CONCURRENCY}, run one after the other.`,
  "",
  "## Result",
  "",
  "| # | Criterion | Value | Result |",
  "|---|---|---|---|",
  `| 1 | Stryker mutants matched (shared mutators) | ${matched.length} / ${strykerShared} = ${pct(matchPct)} (need ≥ 95 %) | ${mark(pass.match)} |`,
  `| 2 | Engine Survived / Stryker Killed, confirmed by the full suite | ${lost.length} of ${candidates.length} candidates (need 0)${baselineCode === 0 ? "" : "; full-suite baseline RED"} | ${mark(pass.lost)} |`,
  `| 3 | Score gap | engine ${pct(engineScore)}, Stryker ${pct(strykerScore)}, gap ${scoreGap === null ? "n/a" : scoreGap.toFixed(2)} (need ≤ 2) | ${mark(pass.score)} |`,
  `| 4 | Wall time | engine ${secs(times["engine"])}, Stryker ${secs(times["stryker"])}, ${speedup.toFixed(1)}× (need ≥ 10×) | ${mark(pass.speed)} |`,
  "",
  "## Per target",
  "",
  "| Target | Stryker mutants | Engine mutants | Matched | Stryker score | Engine score |",
  "|---|---|---|---|---|---|",
  ...perFile,
  "",
  "Scores leave out the verify-callsite mutants the engine marks Ignored (polly#143); the parity run of Stryker does not load the polly ignorer plugin, so it runs them.",
  "",
  `Mutators only Stryker has: ${[...strykerMutators].filter((m) => !engineMutators.has(m)).join(", ") || "none"}. Only the engine: ${[...engineMutators].filter((m) => !strykerMutators.has(m)).join(", ") || "none"}.`,
  "",
  "## Status of matched mutants",
  "",
  "Stryker reports NoCoverage from per-test coverage; the engine has none yet (plan Phase 7), so it runs those mutants and they survive. Both count as undetected in the score.",
  "",
  ...crossTable,
  "",
  `## Unmatched — Stryker only (${strykerOnly.length})`,
  "",
  strykerOnly.length ? `By mutator: ${byMutator(strykerOnly)}.` : "None.",
  "",
  ...(strykerOnly.length
    ? ["| Where | Mutator | Replacement | Status |", "|---|---|---|---|", ...strykerOnly.map(row)]
    : []),
  "",
  `## Unmatched — engine only (${engineOnly.length})`,
  "",
  engineOnly.length ? `By mutator: ${byMutator(engineOnly)}.` : "None.",
  "",
  ...(engineOnly.length
    ? ["| Where | Mutator | Replacement | Status |", "|---|---|---|---|", ...engineOnly.map(row)]
    : []),
  "",
  `## Criterion 2 candidates (${candidates.length})`,
  "",
  candidates.length === 0
    ? "None."
    : "Each candidate ran against the full unit suite with the engine's mutant. Killed by the full suite = a kill the engine's test selection lost.",
  "",
  ...(candidates.length
    ? [
        "| Where | Mutator | Replacement | Full suite |",
        "|---|---|---|---|",
        ...lost.map((p) => `${row(p.engine).replace(/\| Survived \|$/, "| Killed (lost) |")}`),
        ...notLost.map((p) => `${row(p.engine).replace(/\| Survived \|$/, "| Survived |")}`),
      ]
    : []),
  "",
];

if (times["engineFull"] !== undefined) {
  const full = await readReport(join(OUT, "engine-full.json"));
  const s = score(full.mutants.map((m) => m.status));
  lines.push(
    "## Engine alone, every polly.mutate.ts target",
    "",
    `${Object.keys(Object.groupBy(full.mutants, (m) => m.file)).length} targets, ${full.mutants.length} mutants, ${secs(times["engineFull"])} wall, score ${pct(s)} (fast mode, no cache).`,
    ""
  );
}

writeFileSync(RESULTS, `${lines.join("\n")}\n`);
console.log(`\n${lines.slice(6, 14).join("\n")}\n\nwrote ${RESULTS}`);
process.exit(Object.values(pass).every(Boolean) ? 0 : 1);
