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
 *      (the 0.96.0 manifest), installed beside a server app's runtime peer
 *      (elysia). Its node_modules size is
 *      reported for comparison.
 *   3. Install the real tarball beside the same peers. None of the five is in
 *      node_modules; the size is reported and must be smaller.
 *   4. `@fairfox/polly`, `@fairfox/polly/elysia` and `@fairfox/polly/state`
 *      import under bun and node, each exiting by itself within 15 s, with
 *      @automerge/automerge-repo absent from node_modules (asserted).
 *      `@fairfox/polly/bdd` and `@fairfox/polly/mutate` reject, under bun
 *      and node, with the install message naming all of their packages.
 *   5. `polly visualize`, `polly verify`, `polly mutate` and `polly bdd` each
 *      exit non-zero with the message naming its packages and the exact
 *      `bun add -d` command, through the `polly` wrapper and through each
 *      tool's own cli.js; `polly verify --witness` adds the gherkin pair.
 *   6. `polly visualize` with typescript-7 alone, in a separate project that
 *      has only the tarball and `typescript-7` (no elysia, no
 *      @automerge/automerge-repo, no tweetnacl; asserted absent):
 *      `--generate` exits 0 and writes a DSL for examples/minimal and for
 *      the mesh-app fixture (two `$meshState` documents), and
 *      `polly verify --help` exits 0 without gherkin. With that
 *      fixture's `--snapshot`, it exits 1 naming tweetnacl and
 *      @automerge/automerge-repo and the `bun add -d` command; after that
 *      command, it exits 0 and the DSL carries the overlay. 0.97.0 failed
 *      the first `--generate` with "Cannot find package 'tweetnacl'".
 *   7. Install the five as devDependencies (the command the message prints):
 *      `polly visualize --generate` on a copy of examples/minimal exits 0 and
 *      writes the DSL, and `@fairfox/polly/bdd` imports and parses a feature.
 *
 * Run in one command: `bun scripts/e2e-tool-deps-cold-install.ts`.
 * `POLLY_E2E_TARBALL=<path.tgz>` installs that tarball instead of packing
 * dist/ (to run these checks against a published or older build).
 */

export const capability = "cli.tool-deps-cold-install" as const;

import { cpSync, existsSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { POLLY_PKG_DIR, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import {
  BDD_FEATURE,
  COMMAND_TOOL_PACKAGES,
  commandToolPackages,
  installCommand,
  MUTATE_FEATURE,
  RUNTIME_PEERS,
  TOOL_PACKAGES,
  type ToolPackage,
  VISUALIZE_SNAPSHOT_FEATURE,
} from "../tools/tool-deps/src/index.ts";
import { describe, packageDirs, runAlarmed, staleDist } from "./e2e-analysis-cold-install.ts";

const REPO_ROOT = join(POLLY_PKG_DIR, "../..");
const MINIMAL = join(REPO_ROOT, "examples/minimal");
/** Two `$meshState` documents and a captured runtime snapshot (polly#114, polly#127). */
const MESH_APP = join(POLLY_PKG_DIR, "tools/visualize/src/__tests__/fixtures/mesh-app");
/**
 * The runtime peer a server app installs. @automerge/automerge-repo is left
 * out on purpose: the runtime entries must import without it (step 4). Up to
 * 0.97.1 `@fairfox/polly/elysia` loaded it at import time, through the
 * sweep-sealed module that `bun build` inlined into the entry.
 */
const SERVER_PEERS = { elysia: "1.4.30" };
/** Packages the typescript-7-only visualize project must not contain (step 6). */
const NOT_IN_VIZ_PROJECT = ["elysia", ...Object.keys(RUNTIME_PEERS)];
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

async function writeProject(
  dir: string,
  deps: Record<string, string>,
  devDeps: Record<string, string> = {}
): Promise<void> {
  const pkg = {
    name: "server-app",
    private: true,
    type: "module",
    dependencies: deps,
    devDependencies: devDeps,
  };
  await Bun.write(join(dir, "package.json"), `${JSON.stringify(pkg, null, 2)}\n`);
}

async function install(dir: string): Promise<void> {
  const r = await runAlarmed(["bun", "install"], dir, CLI_ALARM_S);
  assert(r.exitCode === 0, `bun install in ${dir}: ${describe(r)}`);
}

/** `bun pm pack` dist/ into `workDir`/pack; returns the tarball path. */
async function packTarball(ctx: TierContext, workDir: string): Promise<string> {
  ctx.log("[e2e] bun pm pack");
  const packDir = join(workDir, "pack");
  const pack = await runAlarmed(
    ["bun", "pm", "pack", "--destination", packDir],
    POLLY_PKG_DIR,
    CLI_ALARM_S
  );
  assert(pack.exitCode === 0, `bun pm pack: ${describe(pack)}`);
  const tarballName = readdirSync(packDir).find((f) => f.endsWith(".tgz"));
  assert(tarballName !== undefined, `no tarball in ${packDir}`);
  return join(packDir, tarballName);
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

/** Copy the mesh-app fixture's sources, tsconfig and snapshot into `dir`. */
function writeMeshFixture(dir: string): void {
  for (const entry of ["src", "tsconfig.json", "snapshot.json"]) {
    cpSync(join(MESH_APP, entry), join(dir, entry), { recursive: true });
  }
}

/** Run `polly <args>` in `cwd` and require exit 0 and a fresh docs/architecture.dsl; returns the DSL. */
async function visualizeOk(polly: string, cwd: string, args: string[]): Promise<string> {
  const dslPath = join(cwd, "docs/architecture.dsl");
  rmSync(dslPath, { force: true });
  const r = await runAlarmed([polly, ...args], cwd, CLI_ALARM_S);
  assert(r.exitCode === 0, `polly ${args.join(" ")} in ${cwd}: ${describe(r)}`);
  assert(existsSync(dslPath), `polly ${args.join(" ")} wrote no docs/architecture.dsl`);
  return readFileSync(dslPath, "utf8");
}

/**
 * Step 5, from each tool's own cli.js, run without the `polly` wrapper: up to
 * 0.97.1 only the wrapper checked, and a direct run died on "Cannot find
 * module 'typescript-7/ast'" or a raw stack.
 */
async function directCliRuns(ctx: TierContext, app: string): Promise<void> {
  const direct: { command: string; args: string[] }[] = [
    ...Object.keys(COMMAND_TOOL_PACKAGES).map((command) => ({ command, args: [] })),
    { command: "verify", args: ["--witness"] },
  ];
  for (const { command, args } of direct) {
    const label = ["polly", command, ...args].join(" ");
    const packages = commandToolPackages(command, args);
    const cli = join(app, `node_modules/@fairfox/polly/dist/tools/${command}/src/cli.js`);
    ctx.log(`[e2e] bun ${relative(app, cli)} ${args.join(" ")}`);
    const r = await runAlarmed(["bun", cli, ...args], app, CLI_ALARM_S);
    assert(r.exitCode === 1, `${label} via cli.js: ${describe(r)}`);
    assert(r.stderr.includes(`${label} needs `), `${label} via cli.js: no message: ${describe(r)}`);
    assert(
      r.stderr.includes(installCommand(packages)),
      `${label} via cli.js: no "${installCommand(packages)}" in ${describe(r)}`
    );
  }
}

/**
 * Step 6: `polly visualize` in a project with the tarball and typescript-7
 * only. A plain `--generate` needs nothing else, mesh documents included;
 * `--snapshot` names its two runtime peers until they are installed.
 */
async function visualizeWithTypescriptOnly(
  ctx: TierContext,
  tarball: string,
  dir: string
): Promise<void> {
  ctx.log("[e2e] separate project: the tarball + typescript-7 only");
  await writeProject(
    dir,
    { "@fairfox/polly": `file:${tarball}` },
    { "typescript-7": specOf("typescript-7") }
  );
  await install(dir);
  const extra = packageDirs(join(dir, "node_modules"))
    .filter((p) => NOT_IN_VIZ_PROJECT.some((n) => p.endsWith(`/node_modules/${n}`)))
    .map((p) => relative(dir, p));
  assert(extra.length === 0, `the typescript-7-only project has:\n${extra.join("\n")}`);
  const polly = join(dir, "node_modules/.bin/polly");

  ctx.log("[e2e] polly visualize --generate on examples/minimal (typescript-7 only)");
  const minimal = join(dir, "minimal");
  writeFixture(minimal);
  const minimalDsl = await visualizeOk(polly, minimal, ["visualize", "--generate"]);
  ctx.log(`[e2e]   ${minimalDsl.split("\n").length}-line DSL`);

  ctx.log("[e2e] polly visualize --generate on the $meshState fixture (typescript-7 only)");
  const mesh = join(dir, "mesh");
  writeMeshFixture(mesh);
  const meshDsl = await visualizeOk(polly, mesh, ["visualize", "--generate"]);
  assert(meshDsl.includes("mesh_doc_chat_rooms"), "mesh DSL has no mesh_doc_chat_rooms node");
  assert(!meshDsl.includes("sync:"), "a DSL generated without --snapshot carries overlay edges");

  // `polly verify` loads gherkin only for --witness; this project has none.
  ctx.log("[e2e] polly verify --help (typescript-7 only) runs without gherkin");
  const help = await runAlarmed([polly, "verify", "--help"], minimal, CLI_ALARM_S);
  assert(help.exitCode === 0, `polly verify --help without gherkin: ${describe(help)}`);
  assert(!`${help.stdout}${help.stderr}`.includes(" needs "), `verify --help: ${describe(help)}`);

  const snapshotArgs = ["visualize", "generate", "--snapshot", "snapshot.json"];
  ctx.log("[e2e] polly visualize --snapshot without tweetnacl / @automerge/automerge-repo");
  rmSync(join(mesh, "docs"), { recursive: true, force: true });
  const missing = await runAlarmed([polly, ...snapshotArgs], mesh, CLI_ALARM_S);
  const out = `${missing.stdout}\n${missing.stderr}`;
  const expected = installCommand(VISUALIZE_SNAPSHOT_FEATURE.packages);
  assert(missing.exitCode === 1, `--snapshot without its peers: ${describe(missing)}`);
  assert(
    out.includes("polly visualize --snapshot needs tweetnacl and @automerge/automerge-repo"),
    `--snapshot: no message naming both peers: ${describe(missing)}`
  );
  assert(out.includes(expected), `--snapshot: no "${expected}" in ${describe(missing)}`);
  assert(!out.includes("Cannot find package"), `--snapshot: bare resolve error: ${out}`);
  assert(!existsSync(join(mesh, "docs/architecture.dsl")), "--snapshot failure wrote a DSL");
  ctx.log(missing.stderr.trim());

  ctx.log(`[e2e] ${expected}`);
  const add = await runAlarmed(expected.split(" "), dir, CLI_ALARM_S);
  assert(add.exitCode === 0, `${expected}: ${describe(add)}`);
  const overlay = await visualizeOk(polly, mesh, snapshotArgs);
  assert(
    /-> extension\.mesh_doc_chat_rooms "has"/.test(overlay),
    "the --snapshot DSL has no overlay edge onto mesh_doc_chat_rooms"
  );
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir("polly-e2e-tool-deps-");
  try {
    const stale = await staleDist();
    assert(stale === null, `${stale}; run \`bun run build:lib\` in packages/polly first`);

    const tarball = process.env["POLLY_E2E_TARBALL"] ?? (await packTarball(ctx, temp.dir));
    ctx.log(`[e2e] tarball: ${tarball}`);

    ctx.log("[e2e] baseline: the five as dependencies (0.96.0 manifest)");
    const before = join(temp.dir, "before");
    await writeProject(before, {
      "@fairfox/polly": `file:${await baselineTarball(tarball, temp.dir)}`,
      ...SERVER_PEERS,
    });
    await install(before);
    const beforeKb = sizeKb(join(before, "node_modules"));
    assert(installedTools(before).length === TOOLS.length, "baseline did not install the five");

    ctx.log("[e2e] install the tarball beside elysia, without the tool packages");
    const app = join(temp.dir, "app");
    await writeProject(app, { "@fairfox/polly": `file:${tarball}`, ...SERVER_PEERS });
    await install(app);
    const present = installedTools(app);
    assert(present.length === 0, `tool packages installed by default:\n${present.join("\n")}`);
    const afterKb = sizeKb(join(app, "node_modules"));
    ctx.log(`[e2e] node_modules: ${mb(beforeKb)} before, ${mb(afterKb)} after`);
    assert(afterKb < beforeKb, `node_modules did not shrink: ${mb(beforeKb)} → ${mb(afterKb)}`);

    assert(
      !existsSync(join(app, "node_modules/@automerge/automerge-repo")),
      "@automerge/automerge-repo is installed; the runtime-entry imports would not prove it optional"
    );
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

    await directCliRuns(ctx, app);

    await visualizeWithTypescriptOnly(ctx, tarball, join(temp.dir, "viz"));

    ctx.log(`[e2e] ${installCommand(TOOLS)}`);
    const add = await runAlarmed(
      ["bun", "add", "-d", ...TOOLS.map((t) => TOOL_PACKAGES[t].install)],
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
