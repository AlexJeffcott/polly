#!/usr/bin/env bun
/**
 * e2e: the polly#114 mesh seed-race guard.
 *
 * Runs MeshSeed.tla — the formal model of Polly's concurrent first-time
 * $meshState seed — through TLC twice, and asserts both outcomes:
 *
 *   1. SeedDeterministic = TRUE  (the shipped polly#113 fix)
 *      → TLC finds no error. The seed converges.
 *
 *   2. SeedDeterministic = FALSE (the pre-fix seed, as restored by
 *      POLLY_113_DISABLE_FIX) → TLC reports a SeedConvergence violation.
 *
 * The second run is the falsification gate: it proves the guard actually
 * catches a regression in the seed path, rather than passing vacuously.
 * If a future change to MeshSeed.tla made the racy seed converge anyway,
 * this script fails — loudly — instead of going quietly green.
 *
 * Usage:  bun scripts/e2e-verify-mesh-seed.ts
 * Needs:  Docker, and the `polly-tla:latest` image (built from
 *         tools/verify/Dockerfile).
 */

import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fail, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { meshSeedCfg, SEED_CONVERGENCE_INVARIANT } from "../tools/verify/src/runner/mesh-seed";

export const capability = "verify.mesh-seed" as const;

const DOCKER_IMAGE = "polly-tla:latest";
const SPEC_DIR = resolve(import.meta.dir, "../tools/verify/specs/tla");

/** Run TLC on MeshSeed.tla with the given cfg; return TLC's stdout+stderr. */
async function runTLC(cfg: string): Promise<string> {
  const work = mkdtempSync(join(tmpdir(), "polly-mesh-seed-"));
  try {
    writeFileSync(join(work, "MeshSeed.tla"), readFileSync(join(SPEC_DIR, "MeshSeed.tla")));
    writeFileSync(join(work, "MeshSeed.cfg"), cfg);
    const proc = Bun.spawn(
      [
        "docker",
        "run",
        "--rm",
        "-v",
        `${work}:/work`,
        DOCKER_IMAGE,
        "tlc",
        "-workers",
        "1",
        "-cleanup",
        "MeshSeed.tla",
      ],
      { stdout: "pipe", stderr: "pipe" }
    );
    const [stdout, stderr] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
    ]);
    await proc.exited;
    return `${stdout}\n${stderr}`;
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    ctx.log("e2e: polly#114 mesh seed-race guard\n");

    const cfgPath = join(SPEC_DIR, "MeshSeed.cfg");
    if (!existsSync(join(SPEC_DIR, "MeshSeed.tla")) || !existsSync(cfgPath)) {
      fail(`MeshSeed.tla / MeshSeed.cfg not found in ${SPEC_DIR}`);
    }
    const baseCfg = readFileSync(cfgPath, "utf8");

    // ── Run 1: the fix in place — the seed must converge ────────────────
    ctx.log("→ SeedDeterministic = TRUE  (polly#113 fix in place)");
    const passOutput = await runTLC(meshSeedCfg(baseCfg, { disableFix: false }));
    if (!passOutput.includes("No error has been found")) {
      ctx.log(passOutput);
      fail("MeshSeed.tla did NOT pass under the fix — the guard is broken.");
    }
    if (passOutput.includes(`Invariant ${SEED_CONVERGENCE_INVARIANT} is violated`)) {
      ctx.log(passOutput);
      fail("SeedConvergence was violated under the fix — the guard is broken.");
    }
    ctx.log("  ✓ seed converges; no invariant violated\n");

    // ── Run 2: the fix disabled — TLC must catch the race ───────────────
    ctx.log("→ SeedDeterministic = FALSE (pre-fix seed — POLLY_113_DISABLE_FIX)");
    const falsifyOutput = await runTLC(meshSeedCfg(baseCfg, { disableFix: true }));
    if (!falsifyOutput.includes(`Invariant ${SEED_CONVERGENCE_INVARIANT} is violated`)) {
      ctx.log(falsifyOutput);
      fail(
        `Expected a ${SEED_CONVERGENCE_INVARIANT} violation under the pre-fix seed, but TLC reported none. The guard would not catch a polly#113 regression.`
      );
    }
    ctx.log(`  ✓ TLC reports the ${SEED_CONVERGENCE_INVARIANT} violation — the race is caught\n`);

    ctx.log("✅ Seed-race guard verified: passes with the fix, fails without it.");
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
