#!/usr/bin/env bun
/**
 * E2e: `polly verify` codegen → TLC roundtrip for a real example project.
 *
 * `e2e-verify-mesh-seed.ts` runs a hand-written TLA spec through TLC, and
 * `e2e-stryker-verify.ts` is mutation testing — neither exercises the full
 * chain the `polly verify` CLI runs for a real consumer: read the handlers
 * and `verification.config.ts`, generate the TLA+ spec, run TLC, report the
 * result. That chain is the core promise of `polly verify`, and nothing
 * drove it end to end against an example.
 *
 * Against `examples/minimal`, using the working-tree CLI:
 *
 *   1. `polly verify` exits 0 and reports "Verification passed". The
 *      generated `UserApp.tla` exists and REFLECTS THE SOURCE — it contains
 *      the handler (`HandlePing`) and the state field (`user_active`) the
 *      example declares, proving codegen read the real project rather than
 *      emitting a canned spec. TLC explored a non-trivial state space.
 *
 *   2. Falsification: take the just-generated spec, inject an always-false
 *      invariant, and run TLC on it directly. TLC must report that invariant
 *      violated — proving the TLC leg genuinely checks the generated spec
 *      rather than rubber-stamping it. (The complementary "catches a real
 *      regression" teeth-check lives in `e2e-verify-mesh-seed.ts`.)
 *
 * Needs: Docker and the `polly-tla:latest` image (as the verify CLI does).
 */

export const capability = "verify.codegen-roundtrip" as const;

import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { runCli } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const DOCKER_IMAGE = "polly-tla:latest";
const MINIMAL_DIR = resolve(import.meta.dir, "../../../examples/minimal");
const GENERATED_DIR = join(MINIMAL_DIR, "specs/tla/generated");
const FALSE_INVARIANT = "PollyE2eAlwaysFalse";

/** Run TLC on a prepared work dir containing UserApp.tla/.cfg (+ deps). */
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

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    // 1. Run the full CLI roundtrip against the example.
    ctx.log("[e2e] polly verify (examples/minimal) — code → TLA+ → TLC");
    const verify = await runCli(["verify"], { cwd: MINIMAL_DIR });
    assert(
      verify.exitCode === 0,
      `polly verify exited ${verify.exitCode}\n${verify.stdout}\n${verify.stderr}`
    );
    const output = `${verify.stdout}\n${verify.stderr}`;
    assert(/Verification passed/i.test(output), `expected "Verification passed"; got:\n${output}`);

    const tlaPath = join(GENERATED_DIR, "UserApp.tla");
    const cfgPath = join(GENERATED_DIR, "UserApp.cfg");
    assert(existsSync(tlaPath), `codegen did not produce ${tlaPath}`);
    assert(existsSync(cfgPath), `codegen did not produce ${cfgPath}`);

    // Codegen must reflect the example's actual handlers + state, not a
    // canned spec.
    const tla = readFileSync(tlaPath, "utf8");
    assert(/HandlePing/.test(tla), "generated spec is missing the example's HandlePing handler");
    assert(/user_active/.test(tla), "generated spec is missing the example's user_active state");

    // TLC must have explored a non-trivial state space.
    const statesMatch = output.match(/States explored:\s*(\d+)/i);
    const states = statesMatch ? Number(statesMatch[1]) : 0;
    assert(states > 1, `TLC explored a trivial state space (${states}); codegen may be empty`);
    ctx.log(`[e2e] roundtrip passed; TLC explored ${states} states`);

    // 2. Falsification: inject an always-false invariant into the generated
    //    spec and run TLC directly. It must catch it.
    ctx.log("[e2e] falsification: injecting an always-false invariant into the generated spec");
    const work = mkdtempSync(join(tmpdir(), "polly-verify-roundtrip-"));
    try {
      cpSync(GENERATED_DIR, work, { recursive: true });

      const workTla = join(work, "UserApp.tla");
      const tlaText = readFileSync(workTla, "utf8");
      // Insert the definition just before the module's trailing ==== line.
      const lastFooter = tlaText.lastIndexOf("\n====");
      assert(lastFooter !== -1, "could not find the module footer to inject into");
      const injected = `${tlaText.slice(0, lastFooter)}\n${FALSE_INVARIANT} == FALSE\n${tlaText.slice(lastFooter + 1)}`;
      writeFileSync(workTla, injected);

      const workCfg = join(work, "UserApp.cfg");
      const cfgText = readFileSync(workCfg, "utf8");
      writeFileSync(workCfg, cfgText.replace(/INVARIANTS\n/, `INVARIANTS\n  ${FALSE_INVARIANT}\n`));

      const falsifyOutput = await runTLC(work);
      // TLC reports a state-violated invariant as "Invariant X is violated"
      // and a constant-false one as "The invariant of X is equal to FALSE".
      // Either proves it parsed and evaluated the injected invariant against
      // the generated spec rather than ignoring it.
      const caught = new RegExp(
        `Invariant ${FALSE_INVARIANT} is violated|invariant of ${FALSE_INVARIANT} is equal to FALSE`
      ).test(falsifyOutput);
      assert(
        caught,
        `TLC did not reject the injected invariant — the TLC leg is not actually checking the generated spec.\n${falsifyOutput}`
      );
      ctx.log("[e2e] TLC rejected the injected always-false invariant — the check has teeth");
    } finally {
      rmSync(work, { recursive: true, force: true });
    }

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
