#!/usr/bin/env bun
// parity.ts : run TLC (safety only) on every generated spec set under
// examples/ and record generated / distinct / depth per set. Where the Bun
// checker supports a set, run it too and compare the three counts.
//
// TLC counts are kept in tlc-counts.json, keyed by a hash of the spec files,
// so a run after a checker change does not start TLC again. A set whose spec
// changes gets a new hash and TLC runs for it.
//
// Usage: bun parity.ts [--only SUBSTR] [--tlc-limit SECONDS] [--refresh]
// Exit:  0 when every supported set matches; 1 on any DIFFER or error.
// Needs: Docker and polly-tla:latest; `polly verify` run in each example, so
//        that specs/tla/generated exists.

import { createHash } from "node:crypto";
import { existsSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative, resolve } from "node:path";

const HERE = import.meta.dir;
const ROOT = resolve(HERE, "../../../../..");
const CACHE = join(HERE, "tlc-counts.json");
// Part of the cache key: counts from another worker count are not reused.
const TLC_WORKERS = "workers=1";

// Sets left out of the run, with the reason. A reason is required, so a set
// cannot drop out without a record.
const EXCLUDED: Record<string, string> = {
  "examples/elysia-todo-app/server/specs/tla/generated":
    "TLC does not end: stopped after 6,246 s at 257M distinct states, depth 9 (2026-10-28)",
  "examples/team-task-manager/client/specs/tla/generated":
    "TLC does not end: stopped after 30 min at 99.8M distinct states, depth 10, 54M queued (2026-10-28)",
};


type Counts = { generated: number; distinct: number; depth: number };
type TlcEntry = Counts & { hash: string; seconds: number };
type Row = { set: string; tlc: string; bun: string; verdict: "MATCH" | "DIFFER" | "UNSUPPORTED" | "EXCLUDED" | "ERROR" };

const args = process.argv.slice(2);
const flag = (name: string) => {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : undefined;
};
const only = flag("--only");
const tlcLimit = Number(flag("--tlc-limit") ?? 900);
const refresh = args.includes("--refresh");

function specSets(): string[] {
  const out: string[] = [];
  const walk = (dir: string) => {
    for (const entry of readdirSync(dir)) {
      if (entry === "node_modules" || entry.startsWith(".")) continue;
      const path = join(dir, entry);
      if (!statSync(path).isDirectory()) continue;
      if (readdirSync(path).some((f) => f.endsWith(".cfg"))) out.push(relative(ROOT, path));
      walk(path);
    }
  };
  walk(join(ROOT, "examples"));
  return out.filter((d) => d.includes(join("specs", "tla", "generated"))).sort();
}

// The root module is the one with a .cfg of the same name.
function rootModule(dir: string): string {
  const cfgs = readdirSync(dir).filter((f) => f.endsWith(".cfg") && !f.startsWith("Witness_"));
  if (cfgs.length !== 1) throw new Error(`${dir}: expected one .cfg, found ${cfgs.length}`);
  return (cfgs[0] as string).replace(/\.cfg$/, "");
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

function stage(dir: string): { work: string; module: string; hash: string } {
  const module = rootModule(dir);
  const work = mkdtempSync(join(tmpdir(), "polly-parity-"));
  const hash = createHash("sha256").update(TLC_WORKERS);
  for (const file of readdirSync(dir).filter((f) => f.endsWith(".tla") && !f.startsWith("Witness_")).sort()) {
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
// wall-clock limit that stops the container, and with ONE worker: with
// `-workers auto` the reported depth is not deterministic, because a worker
// can reach a state first by a longer path. mesh-recovery-pair: 20 with one
// worker, 21 and 22 on two `auto` runs; generated and distinct do not change.
async function runTlc(work: string, module: string): Promise<{ counts?: Counts; seconds: number; error?: string }> {
  const name = `polly-parity-${process.pid}-${Date.now()}`;
  const start = performance.now();
  const proc = Bun.spawn(
    [
      "docker", "run", "--rm", "--name", name, "--memory", "4g",
      "-e", "JAVA_TOOL_OPTIONS=-Xmx3072m -XX:+UseParallelGC",
      "-v", `${work}:/work`, "polly-tla:latest",
      "tlc", "-workers", "1", "-cleanup", "-metadir", "/tmp/states", `${module}.tla`,
    ],
    { stdout: "pipe", stderr: "pipe" }
  );
  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    Bun.spawnSync(["docker", "stop", name]);
  }, tlcLimit * 1000);
  const [stdout, stderr] = await Promise.all([new Response(proc.stdout).text(), new Response(proc.stderr).text()]);
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

// tlacheck.ts exits 3 when the spec uses TLA+ it does not support.
function runBun(work: string): { counts?: Counts; seconds?: number; error?: string; unsupported?: boolean } {
  const proc = Bun.spawnSync(["bun", join(HERE, "tlacheck.ts"), "--spec", work], { stdout: "pipe", stderr: "pipe" });
  const out = `${proc.stdout.toString()}\n${proc.stderr.toString()}`;
  const m = out.match(/^(\d+) states generated, (\d+) distinct states found, depth (\d+)/m);
  const wall = out.match(/^wall ([\d.]+) s/m);
  const last = out.trim().split("\n").pop();
  if (proc.exitCode === 3) return { error: last, unsupported: true };
  if (proc.exitCode !== 0 || !m) return { error: `tlacheck.ts exit ${proc.exitCode}: ${last}` };
  return { counts: { generated: Number(m[1]), distinct: Number(m[2]), depth: Number(m[3]) }, seconds: Number(wall?.[1]) };
}

const fmt = (c: Counts) => `${c.generated.toLocaleString("en-GB")} / ${c.distinct.toLocaleString("en-GB")} / ${c.depth}`;
const same = (a: Counts, b: Counts) => a.generated === b.generated && a.distinct === b.distinct && a.depth === b.depth;

const cache: Record<string, TlcEntry> = existsSync(CACHE) ? JSON.parse(readFileSync(CACHE, "utf-8")) : {};
const rows: Row[] = [];

for (const set of specSets().filter((s) => !only || s.includes(only))) {
  if (EXCLUDED[set]) {
    rows.push({ set, tlc: EXCLUDED[set], bun: "-", verdict: "EXCLUDED" });
    continue;
  }
  const { work, module, hash } = stage(join(ROOT, set));
  try {
    let tlc = cache[set];
    if (!tlc || tlc.hash !== hash || refresh) {
      console.error(`[parity] TLC ${set}`);
      const r = await runTlc(work, module);
      if (!r.counts) {
        rows.push({ set, tlc: `${r.error} (${r.seconds} s)`, bun: "-", verdict: "ERROR" });
        continue;
      }
      tlc = { ...r.counts, hash, seconds: r.seconds };
      cache[set] = tlc;
      writeFileSync(CACHE, `${JSON.stringify(cache, null, 2)}\n`);
    }
    const tlcText = `${fmt(tlc)} (${tlc.seconds} s)`;
    console.error(`[parity] Bun ${set}`);
    const bun = runBun(work);
    if (!bun.counts) rows.push({ set, tlc: tlcText, bun: bun.error ?? "", verdict: bun.unsupported ? "UNSUPPORTED" : "ERROR" });
    else {
      const bunText = `${fmt(bun.counts)} (${bun.seconds} s)`;
      rows.push({ set, tlc: tlcText, bun: bunText, verdict: same(tlc, bun.counts) ? "MATCH" : "DIFFER" });
    }
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
}

console.log("| Set | TLC generated / distinct / depth | Bun | Verdict |");
console.log("|---|---|---|---|");
for (const r of rows) console.log(`| ${r.set.replace("/specs/tla/generated", "")} | ${r.tlc} | ${r.bun} | ${r.verdict} |`);
process.exit(rows.some((r) => r.verdict !== "MATCH" && r.verdict !== "EXCLUDED") ? 1 : 0);
