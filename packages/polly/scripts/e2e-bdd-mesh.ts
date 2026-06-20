#!/usr/bin/env bun
/**
 * e2e: the mesh BDD scenario, end to end.
 *
 * Runs `mesh-bdd/sync.feature` through the BDD runner with a page-driving world
 * (mesh-bdd/sync.steps.ts): two cold browser peers, a real signalling relay,
 * WebRTC, and Automerge convergence — booted through the documented
 * `createMeshClient` path via the e2e-mesh kit. This is the one BDD scenario
 * that crosses the real process/network/device boundary, the complement to the
 * in-process todo-list pilot (which crosses only the factory boundary). It is
 * the executable-Gherkin face of the existing mesh convergence e2e.
 *
 * Tier-aware: exports `run(ctx)`; needs a browser (registered with
 * needs:["browser"]). Also runnable standalone (`bun scripts/e2e-bdd-mesh.ts`).
 */
import { resolve } from "node:path";
import { runFeatures } from "../tools/bdd/src/run.ts";
import {
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared/contract.ts";

export const capability = "bdd.mesh-sync" as const;

const featureFiles = [resolve(import.meta.dir, "mesh-bdd/sync.feature")];
const stepFiles = [resolve(import.meta.dir, "mesh-bdd/sync.steps.ts")];

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    const result = await runFeatures({ featureFiles, stepFiles });
    ctx.log(
      `[bdd-mesh] ${result.passed} passed, ${result.failed} failed, ${result.undefinedSteps} undefined`
    );
    if (!result.ok) {
      const broken = result.scenarios.find(
        (s) => s.outcome === "fail" || s.outcome === "undefined"
      );
      const step = broken?.steps.find((s) => s.outcome === "fail" || s.outcome === "undefined");
      return {
        pass: false,
        message: `${broken?.feature} › ${broken?.scenario}: ${step?.text ?? "?"} — ${step?.message ?? "failed"}`,
      };
    }
    return { pass: true, detail: { scenarios: result.passed } };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) {
  await selfRun(capability, run);
  // Browsers/relay are closed by the world's teardown; force-exit so any
  // lingering socket handle cannot keep the process alive.
  process.exit(process.exitCode ?? 0);
}
