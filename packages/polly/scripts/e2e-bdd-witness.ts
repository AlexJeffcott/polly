#!/usr/bin/env bun
/**
 * e2e: the BDD ↔ verify reachability witness (`polly verify --witness`), end to
 * end, WITH a falsification gate.
 *
 * The witness asks the formal question the static `polly bdd check` cannot: can
 * the exhaustive model actually reach the outcome a scenario asserts? This
 * script drives the exact codegen the CLI uses — `extractWitnesses` (tools/bdd)
 * to reduce the todo-list scenarios, then `bddPredicateToTLA` /
 * `buildWitnessModule` / `buildWitnessCfg` (tools/verify) over a freshly
 * generated auth subsystem spec — and runs each witness through real TLC.
 *
 *   1. POSITIVE: the real "signed-out user can sign in" scenario reduces to
 *      `user.loggedIn === true && user.role === "admin"`. TLC must report the
 *      witness invariant VIOLATED — the outcome is reachable, the scenario is
 *      honest, and the counterexample is its path through the model.
 *
 *   2. FALSIFICATION: a synthetic lying scenario asserts a guest is logged in
 *      (`user.loggedIn === true && user.role === "guest"`). The login guard
 *      (requires role !== "guest") makes that impossible, so TLC must explore
 *      the whole space and find NO violation — unreachable. This is the gate
 *      that proves the witness has teeth: if a future change let the racy
 *      outcome through, or broke the inversion, this run fails loudly instead
 *      of going quietly green.
 *
 * Usage:  bun scripts/e2e-bdd-witness.ts
 * Needs:  Docker, and the `polly-tla:latest` image (tools/verify/Dockerfile).
 */

import { copyFileSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { extractWitnesses } from "../tools/bdd/src/witness.ts";
import {
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared/contract.ts";
import { generateSubsystemTLA } from "../tools/verify/src/codegen/tla.ts";
import {
  bddPredicateToTLA,
  buildWitnessCfg,
  buildWitnessModule,
  WITNESS_INVARIANT,
  witnessVerdict,
} from "../tools/verify/src/codegen/witness.ts";
import { analyzeCodebase } from "../tools/verify/src/extract/types.ts";
import { DockerRunner } from "../tools/verify/src/runner/docker.ts";

export const capability = "bdd.witness" as const;

const exampleDir = resolve(import.meta.dir, "../../../examples/todo-list");
const messageRouterSpec = resolve(import.meta.dir, "../tools/verify/specs/tla/MessageRouter.tla");
const SUBSYSTEM = "auth";

async function glob(pattern: string): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Bun.Glob(pattern).scan({
    cwd: exampleDir,
    absolute: true,
    onlyFiles: true,
  })) {
    out.push(f);
  }
  return out.sort();
}

/** Generate the auth subsystem spec into `work`, beside MessageRouter.tla. */
async function generateAuthSpec(work: string): Promise<void> {
  const configMod = await import(`file://${join(exampleDir, "specs/verification.config.ts")}`);
  const config = configMod.verificationConfig ?? configMod.default;
  const analysis = await analyzeCodebase({ tsConfigPath: join(exampleDir, "tsconfig.json") });
  const sub = config.subsystems[SUBSYSTEM];
  const { spec, cfg } = await generateSubsystemTLA(SUBSYSTEM, sub, config, analysis);
  writeFileSync(join(work, `UserApp_${SUBSYSTEM}.tla`), spec);
  writeFileSync(join(work, `UserApp_${SUBSYSTEM}.cfg`), cfg);
  copyFileSync(messageRouterSpec, join(work, "MessageRouter.tla"));
}

/** Build a witness module+cfg for `predicate` and run TLC; return TLC's verdict. */
async function runWitness(
  docker: DockerRunner,
  work: string,
  baseCfg: string,
  moduleName: string,
  predicate: string
): Promise<{ reachable: boolean; output: string }> {
  const tla = join(work, `${moduleName}.tla`);
  writeFileSync(
    tla,
    buildWitnessModule(moduleName, `UserApp_${SUBSYSTEM}`, bddPredicateToTLA(predicate))
  );
  writeFileSync(join(work, `${moduleName}.cfg`), buildWitnessCfg(baseCfg));
  const result = await docker.runTLC(tla, { workers: 2, timeout: 180_000 });
  // A violated witness invariant == the outcome is reachable (honest).
  const reachable = !result.success && result.violation?.name === WITNESS_INVARIANT;
  return { reachable, output: result.output };
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const docker = new DockerRunner();
  if (!(await docker.isDockerAvailable())) {
    return { pass: false, message: "Docker not available (needs polly-tla:latest)" };
  }

  // ── 0. The BDD reduction the CLI relies on still finds the auth witness ──
  const featureFiles = await glob("features/**/*.feature");
  const stepFiles = await glob("features/steps.ts");
  const witnesses = await extractWitnesses(featureFiles, stepFiles);
  const signIn = witnesses.find((w) => w.scenario === "A signed-out user can sign in");
  if (signIn?.predicate !== 'user.loggedIn === true && user.role === "admin"') {
    return {
      pass: false,
      message: `expected the sign-in scenario to reduce to the admin predicate, got: ${signIn?.predicate ?? "(none)"}`,
    };
  }
  ctx.log(`[witness] reduced "${signIn.scenario}" → ${signIn.predicate}`);

  const work = mkdtempSync(join(tmpdir(), "polly-bdd-witness-"));
  try {
    await generateAuthSpec(work);
    const baseCfg = await Bun.file(join(work, `UserApp_${SUBSYSTEM}.cfg`)).text();

    // ── 1. POSITIVE: the real scenario's outcome must be reachable ──
    ctx.log("→ positive: the honest sign-in outcome");
    const honest = await runWitness(docker, work, baseCfg, "Witness_honest", signIn.predicate);
    if (!honest.reachable) {
      ctx.log(honest.output);
      return { pass: false, message: "the honest admin-login outcome was reported UNREACHABLE" };
    }
    ctx.log("  ✓ reachable — TLC violates the witness (the outcome is on a real path)\n");

    // ── 2. FALSIFICATION: a lying scenario's outcome must be unreachable ──
    ctx.log("→ falsification: a guest can never be logged in (login guard)");
    const lie = 'user.loggedIn === true && user.role === "guest"';
    const lying = await runWitness(docker, work, baseCfg, "Witness_lie", lie);
    if (lying.reachable) {
      ctx.log(lying.output);
      return {
        pass: false,
        message: "a guest-logged-in outcome was reported reachable — the witness has no teeth",
      };
    }
    if (!lying.output.includes("No error has been found")) {
      ctx.log(lying.output);
      return {
        pass: false,
        message: "TLC did not complete a full exploration for the lying witness",
      };
    }
    ctx.log(
      "  ✓ unreachable — TLC explores the whole space and finds no path (the lie is caught)\n"
    );

    // ── 3. FORBIDDEN polarity: the verdict inverts on the same TLC facts ──
    // A @forbidden scenario asserts a state must be unreachable. The exact same
    // reachability facts from runs 1–2 must produce the opposite verdict.
    ctx.log("→ forbidden polarity: the @forbidden verdict is the dual");
    const guestExcluded = witnessVerdict("forbidden", lying.reachable); // unreachable → pass
    const adminViolated = witnessVerdict("forbidden", honest.reachable); // reachable → fail
    if (!(guestExcluded.ok && guestExcluded.status === "excluded")) {
      return {
        pass: false,
        message: `@forbidden over an unreachable state should pass as "excluded", got ${guestExcluded.status}/${guestExcluded.ok}`,
      };
    }
    if (adminViolated.ok || adminViolated.status !== "violated") {
      return {
        pass: false,
        message: `@forbidden over a reachable state should fail as "violated", got ${adminViolated.status}/${adminViolated.ok}`,
      };
    }
    ctx.log("  ✓ a forbidden-but-unreachable state passes; a forbidden-but-reachable one fails\n");

    ctx.log(
      "✅ Witness verified: honest outcomes reachable, lying outcomes caught, forbidden states excluded."
    );
    return { pass: true, detail: { predicate: signIn.predicate } };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
}

if (import.meta.main) {
  await selfRun(capability, run);
  process.exit(process.exitCode ?? 0);
}
