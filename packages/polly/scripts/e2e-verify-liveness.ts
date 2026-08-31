#!/usr/bin/env bun
/**
 * E2e: the polly#171 routing wedge, and the two changes that close it.
 *
 * `requires()` used to be compiled into the DELIVERY action rather than into a
 * guard the router could route around. With the port connected and the
 * precondition false, the THEN arm of the delivery condition was false and the
 * ELSE arm was unreachable — its condition had already succeeded — so
 * `\E target` had no witness and `UserRouteMessage` was DISABLED. The message
 * stayed "pending" for ever and no action in the model could move it.
 *
 * Nothing observed that, for two compounding reasons: every generated property
 * was a SAFETY property, and a safety property is true of a system that does
 * nothing at all; and the spec carried no fairness for routing, so even a
 * liveness property would have failed on a port-flap cycle first.
 *
 * This harness generates a spec from a handler carrying a `requires()`, then
 * runs TLC over a matrix. The two mutations must FAIL and the intact spec must
 * PASS; a mutation that passes means the corresponding half of the fix is not
 * load-bearing and the wedge could return unseen.
 *
 *   | mutation                        | expected |
 *   |---------------------------------|----------|
 *   | none                            | passes   |
 *   | drop `ENABLED StateTransition`  | violated — the wedge |
 *   | drop the routing-fairness line  | violated — port-flap cycle |
 *
 * Needs: Docker and the `polly-tla:latest` image.
 */

export const capability = "verify.liveness" as const;

import { copyFileSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { analyzeCodebase } from "../tools/analysis/src/extract/types";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { generateTLA } from "../tools/verify/src/codegen/tla";
import type { VerificationConfig } from "../tools/verify/src/types";

const DOCKER_IMAGE = "polly-tla:latest";
const ROUTER_TLA = resolve(import.meta.dir, "../tools/verify/specs/tla/MessageRouter.tla");

/** A handler whose `requires()` can be false while its port is connected. */
const HANDLERS = `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare function requires(cond: boolean, msg?: string): void;
declare const bus: { on: <T>(type: string, fn: (payload: T) => void) => void };

const queue = $sharedState("queue", { draining: false, done: false });

bus.on("COMPLETE_DRAINING", () => {
  requires(queue.value.draining === true, "must be draining");
  queue.value = { draining: false, done: true };
});
`;

const CONFIG: VerificationConfig = {
  state: {
    queue: { draining: { type: "boolean" }, done: { type: "boolean" } },
  } as unknown as VerificationConfig["state"],
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn",
  onRelease: "error",
  liveness: true,
};

async function runTLC(workDir: string): Promise<string> {
  const proc = Bun.spawn(
    [
      "docker",
      "run",
      "--rm",
      "-v",
      `${workDir}:/work`,
      DOCKER_IMAGE,
      "tlc",
      "-workers",
      "1",
      "-cleanup",
      "UserApp.tla",
    ],
    { stdout: "pipe", stderr: "pipe" }
  );
  const [stdout, stderr] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  await proc.exited;
  return `${stdout}\n${stderr}`;
}

/** TLC reports a failed temporal property as "Temporal properties were violated". */
function violated(output: string): boolean {
  return /Temporal propert(y|ies) .*violated|Temporal properties were violated/i.test(output);
}

function errored(output: string): boolean {
  return /Error: |is either undefined or not an operator|unexpected exception/i.test(output);
}

async function checkSpec(spec: string, cfg: string): Promise<string> {
  const work = mkdtempSync(join(tmpdir(), "polly-liveness-"));
  try {
    writeFileSync(join(work, "UserApp.tla"), spec);
    writeFileSync(join(work, "UserApp.cfg"), cfg);
    copyFileSync(ROUTER_TLA, join(work, "MessageRouter.tla"));
    return await runTLC(work);
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const projectDir = mkdtempSync(join(tmpdir(), "polly-liveness-src-"));
  try {
    writeFileSync(
      join(projectDir, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { target: "ES2020", module: "ESNext", strict: true },
        include: ["*.ts"],
      })
    );
    writeFileSync(
      join(projectDir, "package.json"),
      JSON.stringify({ name: "p", version: "0.0.1" })
    );
    writeFileSync(join(projectDir, "handlers.ts"), HANDLERS);

    const analysis = await analyzeCodebase({ tsConfigPath: join(projectDir, "tsconfig.json") });
    const { spec, cfg } = await generateTLA(CONFIG, analysis);

    // The two halves must actually be in the generated spec.
    assert(
      spec.includes("ENABLED StateTransition"),
      "generated spec has no ENABLED guard — the delivery condition is not total"
    );
    assert(
      spec.includes("WF_allVars(UserRouteMessage(i))"),
      "generated spec has no routing fairness"
    );
    assert(
      cfg.includes("NoMessageStaysPending"),
      "generated cfg does not check the liveness property"
    );
    // TLC refuses a temporal formula quantifying over a VARIABLE.
    assert(
      !spec.includes("\\A i \\in 1..Len(messages)"),
      "liveness quantifier ranges over a variable; it must use the constant 1..MaxMessages"
    );

    // 1. Intact — must pass.
    ctx.log("[e2e] TLC: intact spec (ENABLED guard + routing fairness)");
    const intact = await checkSpec(spec, cfg);
    assert(!errored(intact), `TLC errored on the intact spec:\n${intact}`);
    assert(
      !violated(intact),
      `the liveness property failed on the intact spec — the fix is incomplete\n${intact}`
    );
    ctx.log("[e2e] intact spec passes");

    // 2. Drop the ENABLED guard — the wedge must reappear.
    ctx.log("[e2e] falsification: dropping the ENABLED guard");
    const noGuard = spec.replace(/\n\s*\/\\ ENABLED StateTransition\(target, msg\.msgType\)/, "");
    assert(noGuard !== spec, "could not remove the ENABLED guard — the mutation is a no-op");
    const guardResult = await checkSpec(noGuard, cfg);
    assert(
      violated(guardResult),
      `TLC did NOT report a liveness violation without the ENABLED guard. ` +
        `The guard is not load-bearing, so the routing wedge could return unseen.\n${guardResult}`
    );
    ctx.log("[e2e] without the guard TLC reports the wedge — the guard is load-bearing");

    // 3. Drop routing fairness — a port-flap cycle must be found.
    ctx.log("[e2e] falsification: dropping the routing-fairness conjunct");
    const noFairness = spec.replace(
      /\n\s*\/\\ \\A i \\in 1\.\.MaxMessages : WF_allVars\(UserRouteMessage\(i\)\)/,
      ""
    );
    assert(noFairness !== spec, "could not remove the fairness conjunct — the mutation is a no-op");
    const fairnessResult = await checkSpec(noFairness, cfg);
    assert(
      violated(fairnessResult),
      `TLC did NOT report a liveness violation without routing fairness. ` +
        `WF_allVars(UserNext) alone asks only that SOME step happen, which a ` +
        `port flapping for ever satisfies while a message sits pending.\n${fairnessResult}`
    );
    ctx.log("[e2e] without fairness TLC reports the port-flap cycle — fairness is load-bearing");

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(projectDir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
