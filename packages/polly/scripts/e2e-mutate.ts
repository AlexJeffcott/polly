#!/usr/bin/env bun
/**
 * e2e: `polly mutate run` (the Bun-native engine, the default), from cold
 * state, through both CLIs a user can reach — the working-tree `cli/polly.ts`
 * and the built `dist/cli/polly.js` that ships. The built one matters on its
 * own: it finds the injection preload at a different path
 * (dist/tools/mutate/src/engine).
 *
 * A throwaway consumer project — no cache, no report, and a node_modules that
 * holds only @fairfox/polly (linked to this package, as an install would) so
 * its `polly.mutate.ts` imports `defineMutation` from "@fairfox/polly/mutate"
 * — with a state machine whose `requires`/`ensures` callsites sit next to
 * real logic, and a test that pins one branch but not the other. Each CLI must:
 *
 *   1. exit 0 and write reports/mutation/mutation.json;
 *   2. report the verify-callsite mutants as Ignored (polly#143), never run;
 *   3. kill mutants on the tested branch — the falsification gate: if the
 *      preload stopped injecting, nothing would be killed;
 *   4. leave mutants on the untested branch Survived;
 *   5. render the report through `polly mutate report`.
 *
 * Then `--since HEAD` in a git checkout: no change → nothing runs; one target
 * edited → only that target runs.
 *
 * Then the two ways a project gets a config: `polly mutate init` in a project
 * with none, and a Stryker-only project — which runs with a deprecation
 * notice, then `polly mutate migrate --write` gives it a polly.mutate.ts that
 * runs without one and yields the same statuses.
 *
 * Usage:  bun scripts/e2e-mutate.ts
 * Needs:  `bun run build:lib` first (drives dist/cli/polly.js).
 */

import { existsSync, mkdirSync, symlinkSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { isRecord } from "../src/shared/lib/guards";
import { POLLY_PKG_DIR, runBun, withTempDir } from "../tools/test/src/e2e-cli";
import {
  assert,
  fail,
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared";

export const capability = "mutate.engine" as const;

const SOURCE_CLI = resolve(POLLY_PKG_DIR, "cli/polly.ts");
const BUILT_CLI = resolve(POLLY_PKG_DIR, "dist/cli/polly.js");

const POLLY_CONFIG = [
  'import { defineMutation } from "@fairfox/polly/mutate";',
  "export default defineMutation({",
  '  targets: ["src/**/*.ts"],',
  '  tests: { include: ["tests/**/*.test.ts"] },',
  "});",
].join("\n");

const STRYKER_CONFIG = JSON.stringify({
  testRunner: "bun",
  bun: { testFiles: ["tests/**/*.test.ts"] },
  mutate: ["src/**/*.ts"],
});

/** The project without a mutation config. */
const SOURCES: Record<string, string> = {
  "package.json": JSON.stringify({ name: "mutate-e2e", private: true, type: "module" }),
  "src/machine.ts": [
    "const requires = (_c: boolean, _m: string) => {};",
    "const ensures = (_c: boolean, _m: string) => {};",
    "export function transition(state: string, label: string): string {",
    '  requires(state === "idle" || state === "running", "pre: known state");',
    '  const next = label === "go" ? "running" : "idle";',
    '  ensures(next === "running" || next === "idle", "post: settled");',
    "  return next;",
    "}",
    "export function describe(state: string): string {",
    '  return state === "running" ? "busy" : "free";',
    "}",
  ].join("\n"),
  "src/other.ts": "export const double = (n: number) => n * 2;",
  // Pins transition() both ways; never calls describe(), so its mutants survive.
  "tests/machine.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { transition } from "../src/machine.ts";',
    'test("go runs", () => expect(transition("idle", "go")).toBe("running"));',
    'test("stop idles", () => expect(transition("running", "stop")).toBe("idle"));',
  ].join("\n"),
  "tests/other.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { double } from "../src/other.ts";',
    'test("double", () => expect(double(2)).toBe(4));',
  ].join("\n"),
};

const FILES: Record<string, string> = { ...SOURCES, "polly.mutate.ts": POLLY_CONFIG };

/** Write `files` into `dir` and link @fairfox/polly into its node_modules. */
async function writeProject(dir: string, files: Record<string, string>): Promise<void> {
  for (const [rel, content] of Object.entries(files)) await Bun.write(join(dir, rel), content);
  const link = join(dir, "node_modules/@fairfox/polly");
  mkdirSync(dirname(link), { recursive: true });
  symlinkSync(POLLY_PKG_DIR, link);
}

const TERNARY_LINE = 5;
const DESCRIBE_LINE = 10;

interface ReportMutant {
  status: string;
  statusReason?: string;
  line: number;
}

async function readMutants(dir: string, file: string): Promise<ReportMutant[]> {
  const path = join(dir, "reports/mutation/mutation.json");
  if (!existsSync(path)) fail(`no report at ${path}`);
  const report: unknown = await Bun.file(path).json();
  if (!isRecord(report) || !isRecord(report["files"])) fail("report has no files record");
  const entry = report["files"][file];
  if (!isRecord(entry) || !Array.isArray(entry["mutants"]))
    fail(`report has no mutants for ${file}`);
  return entry["mutants"].flatMap((m: unknown) => {
    if (!isRecord(m) || typeof m["status"] !== "string" || !isRecord(m["location"])) return [];
    const start = m["location"]["start"];
    if (!isRecord(start) || typeof start["line"] !== "number") return [];
    const reason = typeof m["statusReason"] === "string" ? m["statusReason"] : undefined;
    return [
      { status: m["status"], line: start["line"], ...(reason ? { statusReason: reason } : {}) },
    ];
  });
}

async function mutate(cli: string, dir: string, args: string[]) {
  const r = await runBun([cli, "mutate", ...args], { cwd: dir });
  assert(
    r.exitCode === 0,
    `polly mutate ${args.join(" ")} exited ${r.exitCode}\n${r.stdout}\n${r.stderr}`
  );
  return r.stdout;
}

async function checkCli(ctx: TierContext, label: string, cli: string): Promise<void> {
  const temp = withTempDir(`polly-e2e-mutate-${label}-`);
  try {
    await writeProject(temp.dir, FILES);
    ctx.log(`[e2e] ${label}: polly mutate run`);
    const out = await mutate(cli, temp.dir, ["run", "--no-report"]);
    assert(/mutants in/.test(out), `the bun engine did not run by default:\n${out}`);

    const mutants = await readMutants(temp.dir, "src/machine.ts");
    const ignored = mutants.filter((m) => m.status === "Ignored");
    assert(ignored.length > 0, "no verify-callsite mutants were reported Ignored");
    assert(
      ignored.every(
        (m) => (m.line === 4 || m.line === 6) && (m.statusReason ?? "").includes("polly#143")
      ),
      `Ignored mutants outside requires/ensures: ${JSON.stringify(ignored)}`
    );
    const killedOnTernary = mutants.filter((m) => m.line === TERNARY_LINE && m.status === "Killed");
    assert(
      killedOnTernary.length > 0,
      `nothing killed on the tested ternary (line ${TERNARY_LINE}) — is the preload injecting?`
    );
    const survivedOnDescribe = mutants.filter(
      (m) => m.line === DESCRIBE_LINE && m.status === "Survived"
    );
    assert(
      survivedOnDescribe.length > 0,
      `nothing survived on the untested describe() (line ${DESCRIBE_LINE})`
    );
    ctx.log(
      `  ✓ ${mutants.length} mutants: ${ignored.length} ignored, ${killedOnTernary.length} killed on the tested branch, ${survivedOnDescribe.length} survived on the untested one`
    );

    const rendered = await mutate(cli, temp.dir, ["report"]);
    assert(
      /MUTATION\s+score/.test(rendered),
      `polly mutate report did not render a score:\n${rendered}`
    );
    ctx.log("  ✓ polly mutate report renders the engine's report");
  } finally {
    temp.cleanup();
  }
}

async function checkSince(ctx: TierContext): Promise<void> {
  const temp = withTempDir("polly-e2e-mutate-since-");
  try {
    await writeProject(temp.dir, FILES);
    const git = async (...args: string[]) => {
      const proc = Bun.spawn(
        ["git", "-c", "user.email=e2e@polly", "-c", "user.name=e2e", ...args],
        {
          cwd: temp.dir,
          stdout: "ignore",
          stderr: "pipe",
        }
      );
      const code = await proc.exited;
      assert(code === 0, `git ${args.join(" ")} failed: ${await new Response(proc.stderr).text()}`);
    };
    await git("init", "-q");
    await git("add", ".");
    await git("commit", "-q", "-m", "fixture");

    ctx.log("[e2e] --since HEAD with a clean checkout");
    const clean = await mutate(SOURCE_CLI, temp.dir, ["run", "--since", "HEAD", "--no-report"]);
    assert(
      /no mutate targets changed since HEAD/.test(clean),
      `expected nothing to run:\n${clean}`
    );

    writeFileSync(
      join(temp.dir, "src/other.ts"),
      "export const double = (n: number) => n * 2 + 0;\n"
    );
    ctx.log("[e2e] --since HEAD after editing src/other.ts");
    const edited = await mutate(SOURCE_CLI, temp.dir, ["run", "--since", "HEAD", "--no-report"]);
    assert(/1 target\(s\)/.test(edited), `expected exactly one target:\n${edited}`);
    const otherMutants = await readMutants(temp.dir, "src/other.ts");
    assert(otherMutants.length > 0, "the edited target was not mutated");
    ctx.log("  ✓ --since runs only what changed");
  } finally {
    temp.cleanup();
  }
}

function statusCounts(mutants: ReportMutant[]): string {
  const counts = new Map<string, number>();
  for (const m of mutants) counts.set(m.status, (counts.get(m.status) ?? 0) + 1);
  return JSON.stringify([...counts].sort());
}

async function checkInit(ctx: TierContext): Promise<void> {
  const temp = withTempDir("polly-e2e-mutate-init-");
  try {
    await writeProject(temp.dir, SOURCES);
    ctx.log("[e2e] built: polly mutate init, then run");
    await mutate(BUILT_CLI, temp.dir, ["init"]);
    const config = await Bun.file(join(temp.dir, "polly.mutate.ts")).text();
    assert(
      config.includes('from "@fairfox/polly/mutate"'),
      `init did not import the package export:\n${config}`
    );
    await mutate(BUILT_CLI, temp.dir, ["run", "--no-report"]);
    const mutants = await readMutants(temp.dir, "src/machine.ts");
    assert(
      mutants.some((m) => m.status === "Killed"),
      "the init config ran but killed nothing"
    );
    ctx.log(`  ✓ init writes a polly.mutate.ts that runs (${mutants.length} mutants)`);
  } finally {
    temp.cleanup();
  }
}

async function checkMigrate(ctx: TierContext): Promise<void> {
  const temp = withTempDir("polly-e2e-mutate-migrate-");
  try {
    await writeProject(temp.dir, { ...SOURCES, "stryker.conf.json": STRYKER_CONFIG });
    ctx.log("[e2e] built: a Stryker-only project runs, with a deprecation notice");
    const legacy = await mutate(BUILT_CLI, temp.dir, ["run", "--no-report"]);
    assert(/deprecated: reading stryker\.conf\.json/.test(legacy), `no notice:\n${legacy}`);
    const before = statusCounts(await readMutants(temp.dir, "src/machine.ts"));

    ctx.log("[e2e] built: polly mutate migrate --write, then run");
    await mutate(BUILT_CLI, temp.dir, ["migrate", "--write"]);
    assert(
      existsSync(join(temp.dir, "polly.mutate.ts")),
      "migrate --write wrote no polly.mutate.ts"
    );
    const migrated = await mutate(BUILT_CLI, temp.dir, ["run", "--no-report", "--no-cache"]);
    assert(!/deprecated/.test(migrated), `the migrated config still reads Stryker:\n${migrated}`);
    const after = statusCounts(await readMutants(temp.dir, "src/machine.ts"));
    assert(before === after, `statuses changed across migration: ${before} → ${after}`);
    ctx.log(`  ✓ migrate keeps the result: ${after}`);
  } finally {
    temp.cleanup();
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    if (!existsSync(BUILT_CLI))
      fail(`Built CLI not found at ${BUILT_CLI}. Run \`bun run build:lib\` first.`);
    await checkCli(ctx, "source", SOURCE_CLI);
    await checkCli(ctx, "built", BUILT_CLI);
    await checkSince(ctx);
    await checkInit(ctx);
    await checkMigrate(ctx);
    ctx.log("\n✅ OK mutate e2e\n");
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
