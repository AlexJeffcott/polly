/**
 * e2e: the BDD stratum, end to end.
 *
 * Runs the todo-list `.feature` files across the REAL factory boundary
 * (createBackground + the shared registerTodoHandlers + state signals) and then
 * cross-checks every scenario against that example's verification config. One
 * command, one PASS/FAIL — the artefact the next session runs to see the whole
 * BDD ↔ verify link still holds, not "well, the unit tests pass".
 *
 * Tier-aware: exports `run(ctx)`; also runnable standalone (`bun scripts/e2e-bdd.ts`).
 */
import { resolve } from "node:path";
import { Glob } from "bun";
import { checkAgainstVerify } from "../tools/bdd/src/check-verify.ts";
import { runFeatures } from "../tools/bdd/src/run.ts";
import {
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared/contract.ts";

const CAPABILITY = "bdd-todo-list";
const exampleDir = resolve(import.meta.dir, "../../../examples/todo-list");

async function glob(pattern: string): Promise<string[]> {
  const out: string[] = [];
  for await (const f of new Glob(pattern).scan({
    cwd: exampleDir,
    absolute: true,
    onlyFiles: true,
  })) {
    out.push(f);
  }
  return out.sort();
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const featureFiles = await glob("features/**/*.feature");
  const stepFiles = await glob("features/steps.ts");
  if (featureFiles.length === 0 || stepFiles.length === 0) {
    return { pass: false, message: `no features/steps under ${exampleDir}` };
  }

  // 1. Run the scenarios across the real boundary.
  const result = await runFeatures({ featureFiles, stepFiles });
  ctx.log(
    `[bdd] ${result.passed} passed, ${result.failed} failed, ${result.undefinedSteps} undefined, ${result.deferred} deferred`
  );
  if (!result.ok) {
    const broken = result.scenarios.find((s) => s.outcome === "fail" || s.outcome === "undefined");
    return {
      pass: false,
      message: `scenario failed: ${broken?.feature} › ${broken?.scenario}`,
      detail: { passed: result.passed, failed: result.failed },
    };
  }

  // 2. Cross-check the scenarios against the verification config.
  const cross = await checkAgainstVerify({
    featureFiles,
    stepFiles,
    configPath: resolve(exampleDir, "specs/verification.config.ts"),
  });
  const errors = cross.findings.filter((f) => f.kind === "error");
  ctx.log(`[bdd] cross-checked ${cross.checked} scenario(s): ${errors.length} error(s)`);
  if (!cross.ok) {
    return { pass: false, message: `cross-check failed: ${errors[0]?.message}` };
  }

  return {
    pass: true,
    detail: { scenarios: result.passed, deferred: result.deferred, crossChecked: cross.checked },
  };
}

if (import.meta.main) {
  await selfRun(CAPABILITY, run);
  // createBackground wires a MessageRouter that keeps listeners open, so force
  // exit rather than hang on the live handle (the bdd CLI does the same).
  process.exit(process.exitCode ?? 0);
}
