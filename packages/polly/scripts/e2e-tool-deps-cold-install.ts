#!/usr/bin/env bun
/**
 * E2e: a server app's production install of the packed package carries none
 * of the tool packages, and each tool says what to install.
 *
 * `typescript-7`, `oxc-parser`, `weapon-regex`, `@cucumber/gherkin` and
 * `@cucumber/messages` are optional peer dependencies (tools/tool-deps). A
 * consumer upgrading to 0.96.0 found them making up most of a 54 MB
 * production node_modules that its server never loaded. This script installs
 * the packed tarball the way that consumer does and checks, from cold:
 *
 *   1. `bun pm pack` (dist/ must be current; `bun run build:lib` first).
 *   2. Baseline: the same tarball with the five restored to `dependencies`
 *      (the 0.96.0 manifest), installed beside a server app's runtime peers
 *      (elysia, @automerge/automerge-repo). Its node_modules size is
 *      reported for comparison.
 *   3. Install the real tarball beside the same peers. None of the five is in
 *      node_modules; the size is reported and must be smaller.
 *   4. `@fairfox/polly`, `@fairfox/polly/elysia` and `@fairfox/polly/state`
 *      import under bun and node, each exiting by itself within 15 s.
 *      `@fairfox/polly/bdd` and `@fairfox/polly/mutate` reject, under bun
 *      and node, with the install message naming all of their packages.
 *   5. `polly visualize`, `polly verify`, `polly mutate` and `polly bdd` each
 *      exit non-zero with the message naming its packages and the exact
 *      `bun add -d` command.
 *   6. Install the five as devDependencies (the command the message prints):
 *      `polly visualize --generate` on a copy of examples/minimal exits 0 and
 *      writes the DSL, and `@fairfox/polly/bdd` imports and parses a feature.
 *
 * `polly visualize` also needs the optional peer tweetnacl at load time
 * (see e2e-analysis-cold-install.ts); step 6 adds it.
 *
 * Run in one command: `bun scripts/e2e-tool-deps-cold-install.ts`.
 */

export const capability = "cli.tool-deps-cold-install" as const;

import { cpSync, existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { POLLY_PKG_DIR, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import {
  BDD_FEATURE,
  COMMAND_TOOL_PACKAGES,
  installCommand,
  MUTATE_FEATURE,
  TOOL_PACKAGES,
  type ToolPackage,
} from "../tools/tool-deps/src/index.ts";
import { describe, packageDirs, runAlarmed, staleDist } from "./e2e-analysis-cold-install.ts";

const REPO_ROOT = join(POLLY_PKG_DIR, "../..");
const MINIMAL = join(REPO_ROOT, "examples/minimal");
/**
 * The runtime peers a server app installs: elysia, and @automerge/automerge-repo,
 * which `@fairfox/polly/elysia` imports at load time (an optional peer, but
 * not optional for that entry; pre-existing, not this script's subject).
 */
const SERVER_PEERS = { elysia: "1.4.30", "@automerge/automerge-repo": "2.5.6" };
/** `polly visualize` also loads tweetnacl at start-up (see the header). */
const VISUALIZE_PEERS = { tweetnacl: "1.0.3" };
const IMPORT_ALARM_S = 15;
const CLI_ALARM_S = 120;
const TOOLS = Object.keys(TOOL_PACKAGES).filter((k): k is ToolPackage => k in TOOL_PACKAGES);
const RUNTIME_ENTRIES = ["@fairfox/polly", "@fairfox/polly/elysia", "@fairfox/polly/state"];

/** `name@spec` → the spec part (`typescript-7@npm:typescript@7.1.0-beta` → `npm:typescript@7.1.0-beta`). */
function specOf(pkg: ToolPackage): string {
  return TOOL_PACKAGES[pkg].install.slice(pkg.length + 1);
}

function readJson(file: string): Record<string, unknown> {
  const parsed: unknown = JSON.parse(readFileSync(file, "utf8"));
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) {
    throw new Error(`${file} is not a JSON object`);
  }
  return Object.fromEntries(Object.entries(parsed));
}

/** Kilobytes on disk under `dir`, from `du -sk`. */
function sizeKb(dir: string): number {
  const out = Bun.spawnSync(["du", "-sk", dir]).stdout.toString();
  return Number.parseInt(out.split(/\s/)[0] ?? "0", 10);
}

function mb(kb: number): string {
  return `${(kb / 1024).toFixed(1)} MB`;
}

/** Tool packages present anywhere under `dir`/node_modules, as relative paths. */
function installedTools(dir: string): string[] {
  const nodeModules = join(dir, "node_modules");
  return packageDirs(nodeModules)
    .filter((p) =>
      TOOLS.some((t) => p === join(nodeModules, t) || p.endsWith(`/node_modules/${t}`))
    )
    .map((p) => relative(dir, p));
}

async function writeProject(dir: string, deps: Record<string, string>): Promise<void> {
  await Bun.write(
    join(dir, "package.json"),
    `${JSON.stringify({ name: "server-app", private: true, type: "module", dependencies: deps }, null, 2)}\n`
  );
}

async function install(dir: string): Promise<void> {
  const r = await runAlarmed(["bun", "install"], dir, CLI_ALARM_S);
  assert(r.exitCode === 0, `bun install in ${dir}: ${describe(r)}`);
}

/** The tarball with the five tool packages back in `dependencies`: the 0.96.0 manifest. */
async function baselineTarball(tarball: string, workDir: string): Promise<string> {
  const extract = join(workDir, "extract");
  const r1 = await runAlarmed(["mkdir", "-p", extract], workDir, 10);
  assert(r1.exitCode === 0, describe(r1));
  const r2 = await runAlarmed(["tar", "-xzf", tarball, "-C", extract], workDir, 60);
  assert(r2.exitCode === 0, `tar -x: ${describe(r2)}`);
  const pkgPath = join(extract, "package", "package.json");
  const pkg = readJson(pkgPath);
  pkg["dependencies"] = Object.fromEntries(TOOLS.map((t) => [t, specOf(t)]));
  writeFileSync(pkgPath, `${JSON.stringify(pkg, null, 2)}\n`);
  const out = join(workDir, "baseline.tgz");
  const r3 = await runAlarmed(["tar", "-czf", out, "-C", extract, "package"], workDir, 60);
  assert(r3.exitCode === 0, `tar -c: ${describe(r3)}`);
  return out;
}

async function importIn(dir: string, runtime: string, specifier: string) {
  const code = `import(${JSON.stringify(specifier)}).then((m) => console.log(Object.keys(m).length), (e) => { console.error(String(e && e.message)); process.exit(3); })`;
  return runAlarmed([runtime, "-e", code], dir, IMPORT_ALARM_S);
}

/** Copy examples/minimal's sources and specs, tsconfig without the `paths` into this checkout. */
function writeFixture(appDir: string): void {
  for (const sub of ["src", "specs"]) {
    cpSync(join(MINIMAL, sub), join(appDir, sub), { recursive: true });
  }
  const tsconfig = readJson(join(MINIMAL, "tsconfig.json"));
  const options = tsconfig["compilerOptions"];
  if (typeof options === "object" && options !== null) {
    const { paths: _paths, types: _types, ...rest } = Object.fromEntries(Object.entries(options));
    tsconfig["compilerOptions"] = rest;
  }
  writeFileSync(join(appDir, "tsconfig.json"), `${JSON.stringify(tsconfig, null, 2)}\n`);
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir("polly-e2e-tool-deps-");
  try {
    const stale = await staleDist();
    assert(stale === null, `${stale}; run \`bun run build:lib\` in packages/polly first`);

    ctx.log("[e2e] bun pm pack");
    const packDir = join(temp.dir, "pack");
    const pack = await runAlarmed(
      ["bun", "pm", "pack", "--destination", packDir],
      POLLY_PKG_DIR,
      CLI_ALARM_S
    );
    assert(pack.exitCode === 0, `bun pm pack: ${describe(pack)}`);
    const tarballName = readdirSync(packDir).find((f) => f.endsWith(".tgz"));
    assert(tarballName !== undefined, `no tarball in ${packDir}`);
    const tarball = join(packDir, tarballName);

    ctx.log("[e2e] baseline: the five as dependencies (0.96.0 manifest)");
    const before = join(temp.dir, "before");
    await writeProject(before, {
      "@fairfox/polly": `file:${await baselineTarball(tarball, temp.dir)}`,
      ...SERVER_PEERS,
    });
    await install(before);
    const beforeKb = sizeKb(join(before, "node_modules"));
    assert(installedTools(before).length === TOOLS.length, "baseline did not install the five");

    ctx.log("[e2e] install the tarball beside elysia + automerge-repo, without the tool packages");
    const app = join(temp.dir, "app");
    await writeProject(app, { "@fairfox/polly": `file:${tarball}`, ...SERVER_PEERS });
    await install(app);
    const present = installedTools(app);
    assert(present.length === 0, `tool packages installed by default:\n${present.join("\n")}`);
    const afterKb = sizeKb(join(app, "node_modules"));
    ctx.log(`[e2e] node_modules: ${mb(beforeKb)} before, ${mb(afterKb)} after`);
    assert(afterKb < beforeKb, `node_modules did not shrink: ${mb(beforeKb)} → ${mb(afterKb)}`);

    for (const runtime of ["bun", "node"]) {
      for (const specifier of RUNTIME_ENTRIES) {
        ctx.log(`[e2e] ${runtime}: import ${specifier}`);
        const r = await importIn(app, runtime, specifier);
        assert(r.exitCode === 0, `${runtime} import ${specifier}: ${describe(r)}`);
        assert(Number(r.stdout.trim()) > 0, `${runtime} import ${specifier}: no exports`);
      }
    }

    // `@fairfox/polly/mutate` is Bun-only (it imports `bun:sqlite` and `bun`),
    // so node cannot load it with or without its packages; bdd runs on both.
    const libraryChecks = [
      { feature: BDD_FEATURE, runtimes: ["bun", "node"] },
      { feature: MUTATE_FEATURE, runtimes: ["bun"] },
    ];
    for (const { feature, runtimes } of libraryChecks) {
      for (const runtime of runtimes) {
        ctx.log(`[e2e] ${runtime}: import ${feature.name} fails with the install message`);
        const r = await importIn(app, runtime, feature.name);
        const expected = installCommand(feature.packages);
        assert(r.exitCode === 3, `${runtime} import ${feature.name} should reject: ${describe(r)}`);
        assert(
          r.stderr.includes(`${expected}\n`),
          `${runtime} import ${feature.name}: no "${expected}" in\n${r.stderr}`
        );
        if (runtime === "bun") ctx.log(r.stderr.trim());
      }
    }

    const polly = join(app, "node_modules/.bin/polly");
    for (const [command, packages] of Object.entries(COMMAND_TOOL_PACKAGES)) {
      ctx.log(`[e2e] polly ${command} without ${packages.join(", ")}`);
      const r = await runAlarmed([polly, command], app, CLI_ALARM_S);
      const out = `${r.stdout}\n${r.stderr}`;
      assert(r.exitCode !== 0, `polly ${command} exited 0 without its packages: ${describe(r)}`);
      assert(r.exitCode !== 142, `polly ${command} did not exit: ${describe(r)}`);
      assert(
        out.includes(`polly ${command} needs `),
        `polly ${command}: no message: ${describe(r)}`
      );
      assert(
        out.includes(installCommand(packages)),
        `polly ${command}: no "${installCommand(packages)}" in ${describe(r)}`
      );
      ctx.log(r.stderr.trim());
    }

    ctx.log(`[e2e] ${installCommand(TOOLS)} (+ visualize's tweetnacl peer)`);
    const add = await runAlarmed(
      [
        "bun",
        "add",
        "-d",
        ...TOOLS.map((t) => TOOL_PACKAGES[t].install),
        ...Object.entries(VISUALIZE_PEERS).map(([n, v]) => `${n}@${v}`),
      ],
      app,
      CLI_ALARM_S
    );
    assert(add.exitCode === 0, `bun add: ${describe(add)}`);
    assert(installedTools(app).length === TOOLS.length, "the five did not install");

    ctx.log("[e2e] polly visualize --generate on examples/minimal");
    writeFixture(app);
    const viz = await runAlarmed([polly, "visualize", "--generate"], app, CLI_ALARM_S);
    assert(viz.exitCode === 0, `polly visualize --generate: ${describe(viz)}`);
    assert(
      existsSync(join(app, "docs/architecture.dsl")),
      "visualize wrote no docs/architecture.dsl"
    );

    ctx.log("[e2e] bun: import @fairfox/polly/bdd and parse a feature");
    const parse = `import("@fairfox/polly/bdd").then((m) => { const f = m.parseFeatureText("Feature: F\\n  Scenario: S\\n    Given a\\n", "f.feature"); console.log(f.scenarios.length); })`;
    const bdd = await runAlarmed(["bun", "-e", parse], app, IMPORT_ALARM_S);
    assert(bdd.exitCode === 0, `import @fairfox/polly/bdd: ${describe(bdd)}`);
    assert(bdd.stdout.trim() === "1", `parseFeatureText: expected 1 scenario, got ${bdd.stdout}`);

    return { pass: true, message: `node_modules ${mb(beforeKb)} → ${mb(afterKb)}` };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    temp.cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
