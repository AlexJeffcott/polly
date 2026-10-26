#!/usr/bin/env bun
/**
 * E2e: the packed package's analysis commands, from a cold install.
 *
 * The analysis behind `polly verify` and `polly visualize` runs on the
 * TypeScript 7 API (`typescript-7/async`), which spawns a `tsgo` process per
 * CLI run; ts-morph, which bundled TypeScript 6, is gone. Tests inside the
 * repository resolve the working tree. This script proves the published
 * shape instead, the way a consumer gets it:
 *
 *   1. `bun pm pack` the package (dist/ must be current; run `bun run
 *      build:lib` first), the same tarball `npm publish` would upload.
 *   2. Install it into an empty project: no `ts-morph` or `@ts-morph/*`
 *      anywhere under node_modules, and no `typescript` at all (the
 *      `typescript-7` alias is an optional peer; e2e-tool-deps-cold-install.ts
 *      covers the install without the tool packages).
 *   3. Import `@fairfox/polly` and `@fairfox/polly/verify` under bun and
 *      node; each process must exit by itself within 15 s (an open handle
 *      kept the import alive before, see the BroadcastChannel unref fix).
 *   4. Copy examples/todo-list, point it at the tarball (its tsconfig
 *      `paths` into this checkout removed), add the optional tool packages
 *      as devDependencies the way a consumer must, and every installed
 *      `typescript` must be 7.x. Install, and run the installed
 *      `node_modules/.bin/polly verify --estimate`, `polly visualize
 *      --generate` and `polly verify --setup`, each under a 120 s alarm. Each
 *      must exit 0 by itself and leave no TypeScript API server (`tsc --api`,
 *      the native tsgo binary) from this run.
 *
 * Known gap, not this script's subject: `polly visualize` imports
 * `@automerge/automerge-repo/slim` and `tweetnacl` (the polly#127 snapshot
 * overlay, through derive-document-id.ts) at load time, and both are
 * optional peers, so a consumer without them gets "Cannot find module"
 * from `polly visualize`. The app below installs them so the analysis path
 * can be checked.
 *
 * Run in one command: `bun scripts/e2e-analysis-cold-install.ts`.
 */

export const capability = "cli.analysis-cold-install" as const;

import {
  cpSync,
  existsSync,
  readdirSync,
  readFileSync,
  realpathSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { join, relative } from "node:path";
import { Glob } from "bun";
import { POLLY_PKG_DIR, type RunResult, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { TOOL_PACKAGES } from "../tools/tool-deps/src/index.ts";

const REPO_ROOT = join(POLLY_PKG_DIR, "../..");
const EXAMPLE = join(REPO_ROOT, "examples/todo-list");
/** Optional peers `polly visualize` needs at load time (see the header). */
const VISUALIZE_PEERS = { "@automerge/automerge-repo": "2.5.6", tweetnacl: "1.0.3" };
const IMPORT_ALARM_S = 15;
const CLI_ALARM_S = 120;

/** Run `argv` in `cwd` under `perl alarm`: SIGALRM (exit 142) means it did not exit by itself. */
export async function runAlarmed(argv: string[], cwd: string, seconds: number): Promise<RunResult> {
  const proc = Bun.spawn(["perl", "-e", `alarm ${seconds}; exec @ARGV`, ...argv], {
    cwd,
    stdout: "pipe",
    stderr: "pipe",
    env: { ...process.env, NO_COLOR: "1" },
  });
  const [stdout, stderr, exitCode] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  return { exitCode, stdout, stderr };
}

export function describe(r: RunResult): string {
  const timedOut = r.exitCode === 142 ? " (alarm: did not exit by itself)" : "";
  return `exit ${r.exitCode}${timedOut}\n${r.stdout}\n${r.stderr}`;
}

/** Why dist/ cannot be packed as is, or null when it is current. */
export async function staleDist(): Promise<string | null> {
  const stamp = join(POLLY_PKG_DIR, "dist", ".build-stamp");
  if (!existsSync(stamp)) return "dist/ has no completed build";
  const built = statSync(stamp).mtimeMs;
  for (const pattern of ["src/**/*.{ts,tsx,css}", "tools/**/src/**/*.{ts,tsx,css}"]) {
    for await (const file of new Glob(pattern).scan({ cwd: POLLY_PKG_DIR, onlyFiles: true })) {
      if (/(^|\/)(__tests__|test-projects)\/|\.(test|spec)\.tsx?$/.test(file)) continue;
      if (statSync(join(POLLY_PKG_DIR, file)).mtimeMs > built) return `dist/ is older than ${file}`;
    }
  }
  return null;
}

/** Every installed package directory under `nodeModules`, scoped ones included, recursively. */
export function packageDirs(nodeModules: string, out: string[] = []): string[] {
  if (!existsSync(nodeModules)) return out;
  for (const entry of readdirSync(nodeModules)) {
    if (entry === ".bin" || entry === ".cache") continue;
    const dir = join(nodeModules, entry);
    if (entry.startsWith("@")) {
      for (const scoped of readdirSync(dir)) {
        out.push(join(dir, scoped));
        packageDirs(join(dir, scoped, "node_modules"), out);
      }
      continue;
    }
    out.push(dir);
    packageDirs(join(dir, "node_modules"), out);
  }
  return out;
}

function readJson(file: string): Record<string, unknown> {
  const parsed: unknown = JSON.parse(readFileSync(file, "utf8"));
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) {
    throw new Error(`${file} is not a JSON object`);
  }
  return Object.fromEntries(Object.entries(parsed));
}

function record(value: unknown): Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value)
    ? Object.fromEntries(Object.entries(value))
    : {};
}

/**
 * No ts-morph anywhere in the install. With `typescript`, at least one
 * TypeScript and every one 7.x; without, none at all.
 */
function checkInstall(dir: string, typescript: boolean): void {
  const installed = packageDirs(join(dir, "node_modules"));
  const morph = installed.filter((p) => /(^|\/)(ts-morph|@ts-morph)(\/|$)/.test(p));
  assert(morph.length === 0, `ts-morph installed:\n${morph.join("\n")}`);
  const typescripts = installed
    .filter((p) => existsSync(join(p, "package.json")))
    .map((p) => ({ p, pkg: readJson(join(p, "package.json")) }))
    .filter(({ pkg }) => pkg["name"] === "typescript");
  if (!typescript) {
    const found = typescripts.map(({ p }) => relative(dir, p)).join("\n");
    assert(typescripts.length === 0, `typescript installed without being asked for:\n${found}`);
    return;
  }
  assert(typescripts.length > 0, "no typescript installed (typescript-7 alias expected)");
  for (const { p, pkg } of typescripts) {
    assert(
      String(pkg["version"]).startsWith("7."),
      `${relative(dir, p)} is typescript ${String(pkg["version"])}`
    );
  }
}

async function install(dir: string): Promise<void> {
  const r = await runAlarmed(["bun", "install"], dir, CLI_ALARM_S);
  assert(r.exitCode === 0, `bun install in ${dir}: ${describe(r)}`);
}

/**
 * This run's TypeScript 7 API servers still alive. The native binary is
 * `@typescript/typescript-<platform>/lib/tsc --api` (`pgrep tsgo` matches
 * nothing), so match `--api` on a command line that names this run's dir.
 */
async function leftoverApiServers(dirs: string[]): Promise<string> {
  const proc = Bun.spawn(["ps", "-axo", "pid=,command="], { stdout: "pipe", stderr: "pipe" });
  const out = await new Response(proc.stdout).text();
  await proc.exited;
  return out
    .split("\n")
    .filter((line) => /\s--api\b|tsgo/.test(line) && dirs.some((dir) => line.includes(dir)))
    .join("\n");
}

/** Copy the example (sources, specs, config), pointed at the tarball. */
function writeApp(appDir: string, tarball: string): void {
  cpSync(EXAMPLE, appDir, {
    recursive: true,
    filter: (src) => !/\/(node_modules|dist|docs|reports)(\/|$)/.test(relative(REPO_ROOT, src)),
  });
  const pkgPath = join(appDir, "package.json");
  const pkg = readJson(pkgPath);
  pkg["dependencies"] = {
    ...record(pkg["dependencies"]),
    "@fairfox/polly": `file:${tarball}`,
    ...VISUALIZE_PEERS,
  };
  // The tool packages are optional peers: a consumer that runs the analysis
  // commands adds them as devDependencies.
  pkg["devDependencies"] = {
    ...record(pkg["devDependencies"]),
    ...Object.fromEntries(
      Object.entries(TOOL_PACKAGES).map(([name, { install }]) => [
        name,
        install.slice(name.length + 1),
      ])
    ),
  };
  writeFileSync(pkgPath, `${JSON.stringify(pkg, null, 2)}\n`);
  const tsconfigPath = join(appDir, "tsconfig.json");
  const tsconfig = readJson(tsconfigPath);
  const { paths: _paths, ...options } = record(tsconfig["compilerOptions"]);
  tsconfig["compilerOptions"] = options;
  writeFileSync(tsconfigPath, `${JSON.stringify(tsconfig, null, 2)}\n`);
}

const COMMANDS: { argv: string[]; expect: RegExp }[] = [
  { argv: ["verify", "--estimate"], expect: /Per-subsystem summary/ },
  { argv: ["visualize", "--generate"], expect: /Architecture Summary/ },
  { argv: ["verify", "--setup"], expect: /Next steps/ },
];

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir("polly-e2e-cold-install-");
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
    const tarball = readdirSync(packDir).find((f) => f.endsWith(".tgz"));
    assert(tarball !== undefined, `no tarball in ${packDir}`);
    const tarballPath = join(packDir, tarball);

    ctx.log("[e2e] install into an empty project");
    const empty = join(temp.dir, "empty");
    await Bun.write(
      join(empty, "package.json"),
      `${JSON.stringify(
        { name: "cold", private: true, dependencies: { "@fairfox/polly": `file:${tarballPath}` } },
        null,
        2
      )}\n`
    );
    await install(empty);
    checkInstall(empty, false);

    for (const runtime of ["bun", "node"]) {
      for (const specifier of ["@fairfox/polly", "@fairfox/polly/verify"]) {
        ctx.log(`[e2e] ${runtime}: import ${specifier}`);
        const code = `import(${JSON.stringify(specifier)}).then((m) => console.log(Object.keys(m).length))`;
        const r = await runAlarmed([runtime, "-e", code], empty, IMPORT_ALARM_S);
        assert(r.exitCode === 0, `${runtime} import ${specifier}: ${describe(r)}`);
        assert(Number(r.stdout.trim()) > 0, `${runtime} import ${specifier}: no exports`);
      }
    }

    ctx.log("[e2e] examples/todo-list against the tarball");
    const app = join(temp.dir, "app");
    writeApp(app, tarballPath);
    await install(app);
    checkInstall(app, true);
    const polly = join(app, "node_modules/.bin/polly");
    for (const { argv, expect } of COMMANDS) {
      ctx.log(`[e2e] polly ${argv.join(" ")}`);
      const r = await runAlarmed([polly, ...argv], app, CLI_ALARM_S);
      assert(r.exitCode === 0, `polly ${argv.join(" ")}: ${describe(r)}`);
      assert(expect.test(r.stdout), `polly ${argv.join(" ")}: no ${expect} in\n${r.stdout}`);
      const left = await leftoverApiServers([temp.dir, realpathSync(temp.dir)]);
      assert(left === "", `polly ${argv.join(" ")} left a TypeScript API server running:\n${left}`);
    }
    const dsl = readFileSync(join(app, "docs/architecture.dsl"), "utf8");
    assert(/background/.test(dsl), "architecture.dsl has no background context");

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    temp.cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
