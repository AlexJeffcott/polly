#!/usr/bin/env bun
/**
 * Parity gate: the Bun checker (`polly verify --engine bun`) must give TLC's
 * generated / distinct / depth counts on every example spec set.
 *
 * Each example with a `specs/verification.config.ts` is copied with no
 * generated specs and verified through the working-tree CLI with
 * `--engine bun`, so the specs come from the state a fresh checkout has.
 * Each generated set (one per subsystem) is then staged safety-only (the
 * PROPERTIES block dropped) and checked twice:
 *
 *   | checker                          | how                                           |
 *   |----------------------------------|-----------------------------------------------|
 *   | Bun, tools/verify/src/checker    | checker/cli.ts on the staged set, every run   |
 *   | TLC `-workers 1`, polly-tla image | only when the set's hash is not in the cache |
 *
 * TLC counts are kept in e2e-verify-bun-parity.counts.json, keyed by the set
 * and a hash of its staged files. A run with no spec change starts no TLC; a
 * codegen change gives new hashes, TLC runs for those sets, and the file
 * changes in the diff. One worker, because with `-workers auto` TLC's
 * reported depth is not deterministic (mesh-recovery-pair: 20 with one
 * worker, 21 and 22 on two `auto` runs).
 *
 * Falsification (2026-10-29): with the constraint rule broken in
 * checker/check.ts (1 in 1,000 out-of-constraint successors stored and
 * expanded), the gate reported DIFFER on all 3 todo-list sets (auth:
 * 5,458,242 / 290,944 / 8 against TLC's 5,433,816 / 289,440 / 5) and exited 1.
 *
 * Environment: POLLY_PARITY_ONLY=<substring> limits the sets;
 * POLLY_PARITY_REFRESH=1 runs TLC for every set; POLLY_PARITY_TLC_LIMIT is
 * TLC's limit per set in seconds (default 900).
 *
 * Needs: Docker. The polly-tla:latest image is built when it is missing, as
 * `polly verify` builds it.
 */

export const capability = "verify.bun-parity" as const;

import { createHash } from "node:crypto";
import {
  cpSync,
  existsSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative, resolve } from "node:path";
import { stripVTControlCharacters } from "node:util";
import { runCli } from "../tools/test/src/e2e-cli";
import { selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { DockerRunner } from "../tools/verify/src/runner/docker";

const ROOT = resolve(import.meta.dir, "../../..");
const EXAMPLES_DIR = join(ROOT, "examples");
const CACHE = join(import.meta.dir, "e2e-verify-bun-parity.counts.json");
const CHECKER_CLI = join(import.meta.dir, "../tools/verify/src/checker/cli.ts");
const IMAGE = "polly-tla:latest";
// Part of the cache key: counts from another worker count are not reused.
const TLC_WORKERS = "workers=1";

// Examples left out, with the reason. A reason is required, so an example
// cannot drop out of the gate without a record.
const EXCLUDED: Record<string, string> = {
  "examples/elysia-todo-app/server":
    "TLC does not end: stopped after 6,246 s at 257M distinct states, depth 9 (2026-10-28)",
  "examples/team-task-manager/client":
    "TLC does not end: stopped after 30 min at 99.8M distinct states, depth 10, 54M queued (2026-10-28)",
  "examples/webrtc-p2p-chat/client":
    "123,836,552 distinct states on the Bun engine (2026-10-29), 60x minimal; no TLC reference run",
};

type Counts = { generated: number; distinct: number; depth: number };
type TlcEntry = Counts & { hash: string; seconds: number };
type Verdict = "MATCH" | "DIFFER" | "UNSUPPORTED" | "EXCLUDED" | "ERROR";
type Row = { set: string; tlc: string; bun: string; verdict: Verdict };
type Staged = { work: string; module: string; hash: string };

const env = process.env;
const only = env["POLLY_PARITY_ONLY"];
const refresh = env["POLLY_PARITY_REFRESH"] === "1";
const tlcLimit = Number(env["POLLY_PARITY_TLC_LIMIT"] ?? 900);

/** Example directories (relative to the repo root) with a verification config. */
function examples(): string[] {
  const out: string[] = [];
  const walk = (dir: string): void => {
    for (const entry of readdirSync(dir)) {
      if (entry === "node_modules" || entry.startsWith(".")) continue;
      const path = join(dir, entry);
      if (!statSync(path).isDirectory()) continue;
      if (existsSync(join(path, "specs", "verification.config.ts"))) out.push(relative(ROOT, path));
      else walk(path);
    }
  };
  walk(EXAMPLES_DIR);
  return out.sort();
}

/**
 * The example's tracked files, as a fresh checkout has them, in a copy beside
 * the original so tsconfig `paths` resolve as the original's do. Every file:
 * mesh-recovery-pair keeps two handlers in a root `main.ts`.
 */
function copyExample(example: string): string {
  const source = join(ROOT, example);
  const dir = mkdtempSync(join(dirname(source), ".e2e-bun-parity-"));
  const tracked = Bun.spawnSync(["git", "ls-files", "-z", "."], { cwd: source, stdout: "pipe" });
  const files = tracked.stdout.toString().split("\0").filter(Boolean);
  if (tracked.exitCode !== 0 || files.length === 0) throw new Error(`${example}: no tracked files`);
  for (const file of files) cpSync(join(source, file), join(dir, file), { recursive: true });
  if (existsSync(join(source, "node_modules"))) {
    symlinkSync(join(source, "node_modules"), join(dir, "node_modules"));
  }
  return dir;
}

/** Generated spec sets under `dir`: the directories that hold a root .cfg. */
function specSets(dir: string): string[] {
  const out: string[] = [];
  const walk = (path: string): void => {
    const entries = readdirSync(path);
    if (entries.some((f) => f.endsWith(".cfg") && !f.startsWith("Witness_"))) out.push(path);
    for (const entry of entries) {
      if (statSync(join(path, entry)).isDirectory()) walk(join(path, entry));
    }
  };
  if (existsSync(dir)) walk(dir);
  return out.sort();
}

// The root module is the one with a .cfg of the same name.
function rootModule(dir: string): string {
  const cfgs = readdirSync(dir).filter((f) => f.endsWith(".cfg") && !f.startsWith("Witness_"));
  const [cfg] = cfgs;
  if (cfgs.length !== 1 || cfg === undefined) {
    throw new Error(`${dir}: expected one .cfg, found ${cfgs.length}`);
  }
  return cfg.replace(/\.cfg$/, "");
}

// Safety only: drop the PROPERTIES block. Neither checker runs liveness here.
function safetyCfg(cfg: string): string {
  const out: string[] = [];
  let skipping = false;
  for (const line of cfg.split("\n")) {
    if (/^PROPERTIES\b/.test(line)) {
      skipping = true;
      continue;
    }
    if (skipping && (/^\s+\S/.test(line) || line.trim() === "")) continue;
    skipping = false;
    out.push(line);
  }
  return out.join("\n");
}

function stage(dir: string): Staged {
  const module = rootModule(dir);
  const work = mkdtempSync(join(tmpdir(), "polly-parity-"));
  const hash = createHash("sha256").update(TLC_WORKERS);
  const tlaFiles = readdirSync(dir)
    .filter((f) => f.endsWith(".tla") && !f.startsWith("Witness_"))
    .sort();
  for (const file of tlaFiles) {
    const text = readFileSync(join(dir, file), "utf-8");
    hash.update(file).update(text);
    writeFileSync(join(work, file), text);
  }
  const cfg = safetyCfg(readFileSync(join(dir, `${module}.cfg`), "utf-8"));
  hash.update(cfg);
  writeFileSync(join(work, `${module}.cfg`), cfg);
  return { work, module, hash: hash.digest("hex").slice(0, 16) };
}

function parseTlc(out: string): Counts | undefined {
  const states = out.match(/^(\d+) states generated, (\d+) distinct states found/m);
  const depth = out.match(/^The depth of the complete state graph search is (\d+)/m);
  if (!states || !depth) return undefined;
  return { generated: Number(states[1]), distinct: Number(states[2]), depth: Number(depth[1]) };
}

// TLC as polly's runner starts it (tools/verify/src/runner/docker.ts), with a
// wall-clock limit that stops the container.
async function runTlc(
  staged: Staged
): Promise<{ counts?: Counts; seconds: number; error?: string }> {
  const name = `polly-parity-${process.pid}-${Date.now()}`;
  const start = performance.now();
  const proc = Bun.spawn(
    [
      "docker",
      "run",
      "--rm",
      "--name",
      name,
      "--memory",
      "4g",
      "-e",
      "JAVA_TOOL_OPTIONS=-Xmx3072m -XX:+UseParallelGC",
      "-v",
      `${staged.work}:/work`,
      IMAGE,
      "tlc",
      "-workers",
      "1",
      "-cleanup",
      "-metadir",
      "/tmp/states",
      `${staged.module}.tla`,
    ],
    { stdout: "pipe", stderr: "pipe" }
  );
  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    Bun.spawnSync(["docker", "stop", name]);
  }, tlcLimit * 1000);
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  clearTimeout(timer);
  const seconds = Math.round((performance.now() - start) / 100) / 10;
  if (timedOut) return { seconds, error: `TLC stopped at the ${tlcLimit} s limit` };
  const out = `${stdout}\n${stderr}`;
  if (/Error:|violated/.test(out) && !/No error has been found/.test(out)) {
    const line = out.split("\n").find((l) => /Error:|violated/.test(l));
    return { seconds, error: `TLC: ${line?.trim()}` };
  }
  const counts = parseTlc(out);
  return counts ? { counts, seconds } : { seconds, error: "TLC output has no state counts" };
}

// The checker's CLI exits 3 when the spec uses TLA+ it does not support.
function runBun(work: string): {
  counts?: Counts;
  seconds?: number;
  error?: string;
  unsupported?: boolean;
} {
  const proc = Bun.spawnSync(["bun", CHECKER_CLI, "--spec", work], {
    stdout: "pipe",
    stderr: "pipe",
  });
  const out = `${proc.stdout.toString()}\n${proc.stderr.toString()}`;
  const m = out.match(/^(\d+) states generated, (\d+) distinct states found, depth (\d+)/m);
  const wall = out.match(/^wall ([\d.]+) s/m);
  const last = out.trim().split("\n").pop();
  if (proc.exitCode === 3) return { error: last, unsupported: true };
  if (proc.exitCode !== 0 || !m) return { error: `checker exit ${proc.exitCode}: ${last}` };
  return {
    counts: { generated: Number(m[1]), distinct: Number(m[2]), depth: Number(m[3]) },
    seconds: Number(wall?.[1]),
  };
}

const fmt = (c: Counts): string =>
  `${c.generated.toLocaleString("en-GB")} / ${c.distinct.toLocaleString("en-GB")} / ${c.depth}`;
const same = (a: Counts, b: Counts): boolean =>
  a.generated === b.generated && a.distinct === b.distinct && a.depth === b.depth;

function readCache(): Record<string, TlcEntry> {
  return existsSync(CACHE) ? JSON.parse(readFileSync(CACHE, "utf-8")) : {};
}

async function tlcCounts(
  ctx: TierContext,
  key: string,
  staged: Staged,
  cache: Record<string, TlcEntry>
): Promise<TlcEntry | string> {
  const cached = cache[key];
  if (cached && cached.hash === staged.hash && !refresh) return cached;
  const why = refresh ? "POLLY_PARITY_REFRESH" : `hash ${staged.hash} not in the cache`;
  ctx.log(`[parity] TLC ${key} (${why})`);
  const r = await runTlc(staged);
  if (!r.counts) return `${r.error} (${r.seconds} s)`;
  const entry = { ...r.counts, hash: staged.hash, seconds: r.seconds };
  cache[key] = entry;
  writeFileSync(CACHE, `${JSON.stringify(cache, null, 2)}\n`);
  return entry;
}

async function checkSet(
  ctx: TierContext,
  key: string,
  dir: string,
  cache: Record<string, TlcEntry>
): Promise<Row> {
  const staged = stage(dir);
  try {
    const tlc = await tlcCounts(ctx, key, staged, cache);
    if (typeof tlc === "string") return { set: key, tlc, bun: "-", verdict: "ERROR" };
    const tlcText = `${fmt(tlc)} (${tlc.seconds} s)`;
    ctx.log(`[parity] Bun ${key}`);
    const bun = runBun(staged.work);
    if (!bun.counts) {
      const verdict = bun.unsupported ? "UNSUPPORTED" : "ERROR";
      return { set: key, tlc: tlcText, bun: bun.error ?? "", verdict };
    }
    const bunText = `${fmt(bun.counts)} (${bun.seconds} s)`;
    const verdict = same(tlc, bun.counts) ? "MATCH" : "DIFFER";
    return { set: key, tlc: tlcText, bun: bunText, verdict };
  } finally {
    rmSync(staged.work, { recursive: true, force: true });
  }
}

/** Verify a cold copy with `--engine bun`, then compare each generated set. */
async function checkExample(
  ctx: TierContext,
  example: string,
  cache: Record<string, TlcEntry>
): Promise<Row[]> {
  const copy = copyExample(example);
  try {
    ctx.log(`[parity] polly verify --engine bun (${example} copy)`);
    const run = await runCli(["verify", "--engine", "bun"], { cwd: copy });
    const output = stripVTControlCharacters(`${run.stdout}\n${run.stderr}`);
    if (run.exitCode !== 0) {
      const tail = output.trim().split("\n").slice(-15).join("\n");
      return [
        {
          set: example,
          tlc: "-",
          bun: `polly verify exit ${run.exitCode}\n${tail}`,
          verdict: "ERROR",
        },
      ];
    }
    if (/falling back to TLC/i.test(output)) {
      return [
        { set: example, tlc: "-", bun: "polly verify fell back to TLC", verdict: "UNSUPPORTED" },
      ];
    }
    const generated = join(copy, "specs", "tla", "generated");
    const sets = specSets(generated);
    if (sets.length === 0) {
      return [{ set: example, tlc: "-", bun: "no generated spec set", verdict: "ERROR" }];
    }
    const rows: Row[] = [];
    for (const dir of sets) {
      const key = join(example, "specs", "tla", "generated", relative(generated, dir));
      rows.push(await checkSet(ctx, key.replace(/\/$/, ""), dir, cache));
    }
    return rows;
  } finally {
    rmSync(copy, { recursive: true, force: true });
  }
}

function table(rows: Row[]): string {
  const lines = ["| Set | TLC generated / distinct / depth | Bun | Verdict |", "|---|---|---|---|"];
  for (const r of rows) {
    lines.push(
      `| ${r.set.replace("/specs/tla/generated", "")} | ${r.tlc} | ${r.bun} | ${r.verdict} |`
    );
  }
  return lines.join("\n");
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const docker = new DockerRunner();
  if (!(await docker.isDockerAvailable())) return { pass: false, message: "Docker not available" };
  if (!(await docker.hasImage())) {
    ctx.log(`[parity] building ${IMAGE}`);
    await docker.buildImage();
  }
  const cache = readCache();
  const rows: Row[] = [];
  for (const example of examples().filter((e) => !only || e.includes(only))) {
    const reason = EXCLUDED[example];
    if (reason) rows.push({ set: example, tlc: reason, bun: "-", verdict: "EXCLUDED" });
    else rows.push(...(await checkExample(ctx, example, cache)));
  }
  const report = table(rows);
  ctx.log(report);
  const checked = rows.filter((r) => r.verdict !== "EXCLUDED");
  if (checked.length === 0) return { pass: false, message: "no spec set was checked" };
  const failed = checked.filter((r) => r.verdict !== "MATCH");
  if (failed.length > 0) {
    return {
      pass: false,
      message: `${failed.length} of ${checked.length} sets not MATCH:\n${report}`,
    };
  }
  return { pass: true, detail: { matched: checked.length } };
}

if (import.meta.main) await selfRun(capability, run);
