#!/usr/bin/env bun
/**
 * E2e: what `polly verify` reports about a run it just did.
 *
 * Three defects filed together, because together they meant neither the
 * prediction nor the result could be checked against reality.
 *
 *   | issue | defect                                                      |
 *   |-------|-------------------------------------------------------------|
 *   | #181  | no `--memory` and no `-Xmx`: TLC took 25% of whatever Docker |
 *   |       | Desktop was allocated, and a long run was killed by the host |
 *   | #182  | the reported state count was the INITIAL-state count, so an  |
 *   |       | exhausted model and an empty one both printed `8 states ✓`   |
 *   | #183  | `--estimate` omitted the send branching and used the wrong   |
 *   |       | context count, calling an infeasible subsystem feasible      |
 *
 * Unit tests pin each parse and formula against captured text. This harness is
 * the other half: one real TLC run in one real container, with every figure
 * polly prints checked against what TLC actually did. Each part carries a
 * falsification gate — the pre-fix behaviour recomputed over the same run, so a
 * regression is visible as the gate going quiet rather than as a green suite.
 *
 * Needs: Docker and the `polly-tla:latest` image.
 */

export const capability = "verify.run-accounting" as const;

import { copyFileSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { analyzeCodebase } from "../tools/analysis/src/extract/types";
import type { CodebaseAnalysis } from "../tools/analysis/src/types";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { estimateStateSpace } from "../tools/verify/src/analysis/state-space-estimator";
import { generateTLA } from "../tools/verify/src/codegen/tla";
import type { UnifiedVerificationConfig } from "../tools/verify/src/config/types";
import { DockerRunner, type TLCResult } from "../tools/verify/src/runner/docker";
import { jvmHeapArg, parseMemoryBytes } from "../tools/verify/src/runner/memory";
import type { VerificationConfig } from "../tools/verify/src/types";

const ROUTER_TLA = resolve(import.meta.dir, "../tools/verify/specs/tla/MessageRouter.tla");

/** Two handlers over one boolean field: small enough to exhaust in seconds. */
const HANDLERS = `
type Signal<T> = { value: T };
declare function $sharedState<T>(name: string, initial: T): Signal<T>;
declare const bus: { on: <T>(type: string, fn: (payload: T) => void) => void };

const session = $sharedState("session", { active: false });

bus.on("OPEN_SESSION", () => {
  session.value = { active: true };
});

bus.on("CLOSE_SESSION", () => {
  session.value = { active: false };
});
`;

const CONFIG: VerificationConfig = {
  state: {
    // Flattened field name, as `polly verify --setup` writes it: the estimator
    // reads a cardinality off this shape, so `fieldProduct` is a real number
    // rather than the unbounded fallback.
    "session.active": { type: "boolean" },
  } as unknown as VerificationConfig["state"],
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn",
  onRelease: "error",
};

/** Lay a generated spec out where `runTLC` expects it. */
function writeSpecDir(spec: string, cfg: string): string {
  const work = mkdtempSync(join(tmpdir(), "polly-run-accounting-"));
  writeFileSync(join(work, "UserApp.tla"), spec);
  writeFileSync(join(work, "UserApp.cfg"), cfg);
  copyFileSync(ROUTER_TLA, join(work, "MessageRouter.tla"));
  return work;
}

/** Members of a `Name = {a, b, c}` assignment in a `.cfg`. */
function cfgSetMembers(cfg: string, name: string): string[] {
  const match = new RegExp(`^\\s*${name} = \\{([^}]*)\\}`, "m").exec(cfg);
  assert(Boolean(match?.[1]), `no ${name} assignment in the generated cfg`);
  return (match?.[1] ?? "")
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean);
}

/** The heap TLC chose, in MB, from its own banner line. */
function reportedHeapMb(output: string): number {
  const match = /with (\d+)MB heap/.exec(output);
  assert(match?.[1] !== undefined, `TLC printed no heap line:\n${output.slice(0, 2000)}`);
  return Number.parseInt(match?.[1] ?? "0", 10);
}

/**
 * polly#181: the run has a ceiling polly sets, and it moves when polly moves it.
 *
 * Before the fix both runs below reported the same heap — 25% of the Docker
 * Desktop allocation — because neither `--memory` nor `-Xmx` was passed. That
 * is the falsification gate: if the two figures ever agree again, the ceiling
 * has stopped being polly's.
 */
async function checkMemoryCeiling(
  ctx: TierContext,
  docker: DockerRunner,
  specPath: string
): Promise<void> {
  const small = await docker.runTLC(specPath, { workers: 1, memory: "1g" });
  const large = await docker.runTLC(specPath, { workers: 1, memory: "3g" });

  for (const [label, memory, result] of [
    ["1g", "1g", small],
    ["3g", "3g", large],
  ] as const) {
    const memoryBytes = parseMemoryBytes(memory);
    assert(memoryBytes !== null, `${memory} is not a memory size the runner accepts`);
    const expectedHeap = jvmHeapArg(memoryBytes);
    assert(
      result.output.includes(`Picked up JAVA_TOOL_OPTIONS: -Xmx${expectedHeap} -XX:+UseParallelGC`),
      `at --memory ${label} the JVM did not pick up polly's -Xmx${expectedHeap}:\n${result.output.slice(0, 2000)}`
    );
    assert(
      !/throughput optimized\s+garbage collector/i.test(result.output),
      `TLC still asks for -XX:+UseParallelGC at --memory ${label}, so it was not passed`
    );
  }

  const smallHeap = reportedHeapMb(small.output);
  const largeHeap = reportedHeapMb(large.output);
  assert(
    largeHeap > smallHeap,
    `the heap did not move with verification.memory (${smallHeap}MB at 1g, ${largeHeap}MB at 3g). ` +
      "It is being sized from the Docker Desktop allocation again — the polly#181 defect."
  );
  ctx.log(`[e2e] heap tracks verification.memory: ${smallHeap}MB at 1g, ${largeHeap}MB at 3g`);
}

/**
 * polly#182: the reported count is TLC's, from its summary line.
 *
 * The falsification gate recomputes the old parse over the same transcript. It
 * must still return the initial-state count — otherwise this run does not
 * exhibit the defect and the assertions below prove nothing.
 */
function checkStateAccounting(ctx: TierContext, result: TLCResult): number {
  const stats = result.stats;
  assert(stats !== undefined, "an exhaustive run reported no stats at all");

  const summary =
    /^(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue/m.exec(
      result.output
    );
  assert(summary?.[2] !== undefined, "TLC printed no summary line for a completed run");
  const distinctOnTheLine = Number.parseInt(summary?.[2] ?? "-1", 10);

  assert(
    stats?.distinctStates === distinctOnTheLine,
    `reported ${stats?.distinctStates} distinct states, TLC's summary line says ${distinctOnTheLine}`
  );
  assert(
    stats?.exhaustive === true,
    "a completed run with an empty queue was not called exhaustive"
  );
  assert(stats?.statesLeftOnQueue === 0, "a completed run reported states left on the queue");
  assert(stats?.searchDepth !== undefined, "the search depth was not captured");
  assert(
    stats?.noActionEnabled === false,
    "a model with two handlers was reported as having no action enabled"
  );

  // Falsification: the pre-fix parse over the same text.
  const preFix = /(\d+) distinct states/.exec(result.output);
  const preFixCount = Number.parseInt(preFix?.[1] ?? "-1", 10);
  assert(
    preFixCount === stats?.initialStates,
    `the old parse no longer returns the initial-state count (${preFixCount} vs ${stats?.initialStates}); ` +
      "this transcript does not exhibit polly#182, so the assertions above prove nothing"
  );
  assert(
    preFixCount !== distinctOnTheLine,
    `TLC's initial-state count equals its distinct-state count (${preFixCount}) on this run, ` +
      "so the two parses are indistinguishable — pick a spec with more reachable states"
  );

  ctx.log(
    `[e2e] reported ${distinctOnTheLine} distinct states (depth ${stats?.searchDepth}); ` +
      `the pre-fix parse returned ${preFixCount}, the initial-state count`
  );
  return distinctOnTheLine;
}

/**
 * polly#183: the estimate is computed from the quantities the generator emits.
 *
 * The falsification gate is the old formula over the same config: it must still
 * be far below what the run reached, and far below the new figure.
 */
function checkEstimate(
  ctx: TierContext,
  spec: string,
  cfg: string,
  analysis: CodebaseAnalysis,
  actual: number
): void {
  const declared = /UserMessageTypes == \{([^}]*)\}/.exec(spec)?.[1];
  assert(declared !== undefined, "the generated spec declares no UserMessageTypes");
  const handlerCount = declared
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean).length;

  const contexts = cfgSetMembers(cfg, "Contexts").length;
  const tabs = cfgSetMembers(cfg, "Tabs").length;

  const estimate = estimateStateSpace(CONFIG as unknown as UnifiedVerificationConfig, analysis);

  assert(
    estimate.contextCount === contexts,
    `the estimate models ${estimate.contextCount} contexts; the .cfg declares ${contexts}`
  );
  assert(
    estimate.tabCount === tabs,
    `the estimate models ${estimate.tabCount} tabs; the .cfg declares ${tabs}`
  );
  assert(
    estimate.sendBranching === contexts * (2 ** contexts - 1) * tabs * handlerCount,
    `the send branching (${estimate.sendBranching}) does not match the quantifiers UserNext emits`
  );
  assert(
    estimate.estimatedStates <= actual,
    `the estimate (${estimate.estimatedStates}) exceeds the ${actual} states the run reached; ` +
      "it is documented as a lower bound, so this is a defect in the formula"
  );

  // Falsification: the pre-fix formula. contextCount was maxTabs + 1 and the
  // send branching was absent, replaced by permutations(handlers, maxInFlight).
  const maxTabs = CONFIG.messages.maxTabs ?? 1;
  const maxInFlight = CONFIG.messages.maxInFlight ?? 1;
  let permutations = 1;
  for (let i = 0; i < maxInFlight; i++) permutations *= handlerCount - i;
  const preFix = estimate.fieldProduct ** (maxTabs + 1) * permutations;

  assert(
    preFix < estimate.estimatedStates,
    `the old formula (${preFix}) is not below the new one (${estimate.estimatedStates}); ` +
      "this config does not exhibit polly#183, so the assertions above prove nothing"
  );
  ctx.log(
    `[e2e] estimate ${estimate.estimatedStates} (lower bound) against ${actual} reached; ` +
      `the pre-fix formula said ${preFix}`
  );
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const projectDir = mkdtempSync(join(tmpdir(), "polly-run-accounting-src-"));
  let specDir: string | undefined;
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

    specDir = writeSpecDir(spec, cfg);
    const specPath = join(specDir, "UserApp.tla");
    const docker = new DockerRunner();

    ctx.log("[e2e] polly#181: the memory ceiling");
    await checkMemoryCeiling(ctx, docker, specPath);

    ctx.log("[e2e] polly#182: the reported state count");
    const result = await docker.runTLC(specPath, { workers: 1 });
    assert(result.success, `TLC failed on the intact spec: ${result.error ?? "see output"}`);
    const actual = checkStateAccounting(ctx, result);

    ctx.log("[e2e] polly#183: the estimate against the run");
    checkEstimate(ctx, spec, cfg, analysis, actual);

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(projectDir, { recursive: true, force: true });
    if (specDir) rmSync(specDir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
