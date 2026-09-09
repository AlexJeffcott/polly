#!/usr/bin/env bun
/**
 * E2e: `contexts` decides the model TLC actually checks (polly#185).
 *
 * The `Contexts` set was three literal names — `{background, content, popup}` —
 * fixed in the `.cfg` writer when polly modelled a browser extension. Nothing a
 * project declared changed it, so a server or an Electron app paid
 * `fieldProduct^3` for state replicated across two contexts it did not have,
 * and `3 * 7` on every send for source/target pairs that could not occur.
 *
 * A unit test can pin the emitted line. It cannot show that the line is what
 * TLC pays for. This harness generates one spec per declared set from the SAME
 * handlers, runs each in a real container, and reads the distinct-state count
 * TLC reports:
 *
 *   | `Contexts`                     | expected order |
 *   |--------------------------------|----------------|
 *   | `{background, content, popup}` | ~38,000        |
 *   | `{background, content}`        | ~4,900         |
 *   | `{background}`                 | ~370           |
 *
 * The falsification gate is the three counts agreeing: that is the pre-fix
 * behaviour, in which the declared set never reached the `.cfg`.
 *
 * Needs: Docker and the `polly-tla:latest` image.
 */

export const capability = "verify.declared-contexts" as const;

import { copyFileSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { analyzeCodebase } from "../tools/analysis/src/extract/types";
import type { CodebaseAnalysis } from "../tools/analysis/src/types";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { estimateStateSpace } from "../tools/verify/src/analysis/state-space-estimator";
import { DEFAULT_CONTEXTS } from "../tools/verify/src/codegen/model-constants";
import { generateTLA } from "../tools/verify/src/codegen/tla";
import type { UnifiedVerificationConfig } from "../tools/verify/src/config/types";
import { DockerRunner } from "../tools/verify/src/runner/docker";
import type { VerificationConfig } from "../tools/verify/src/types";

const ROUTER_TLA = resolve(import.meta.dir, "../tools/verify/specs/tla/MessageRouter.tla");

/** Two handlers over one boolean field — the shape the ticket measured. */
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

function configFor(contexts?: string[]): VerificationConfig {
  return {
    ...(contexts ? { contexts } : {}),
    state: {
      "session.active": { type: "boolean" },
    } as unknown as VerificationConfig["state"],
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  } as unknown as VerificationConfig;
}

/** Lay a generated spec out where `runTLC` expects it. */
function writeSpecDir(spec: string, cfg: string, label: string): string {
  const work = mkdtempSync(join(tmpdir(), `polly-contexts-${label}-`));
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

type Measured = {
  label: string;
  declared: string[];
  distinct: number;
  depth: number | undefined;
};

/**
 * Generate for one declared set, run it, and check every figure polly reports
 * about that run against the `.cfg` and against TLC's own summary line.
 */
async function measure(
  ctx: TierContext,
  docker: DockerRunner,
  analysis: CodebaseAnalysis,
  contexts: string[]
): Promise<Measured> {
  const label = String(contexts.length);
  const config = configFor(contexts);
  const { spec, cfg } = await generateTLA(config, analysis);

  const emitted = cfgSetMembers(cfg, "Contexts");
  assert(
    emitted.join(",") === contexts.join(","),
    `declared [${contexts.join(", ")}] but the .cfg emits {${emitted.join(", ")}}`
  );

  // The spec must name no member of the set: the whole claim is that one .cfg
  // line sizes the model, so a member leaking into the .tla would break it.
  for (const name of contexts) {
    assert(
      !new RegExp(`\\b${name}\\b`).test(spec),
      `the generated spec names the context "${name}"; the set must reach TLC only through the .cfg`
    );
  }

  const tabs = cfgSetMembers(cfg, "Tabs").length;
  const declaredTypes = /UserMessageTypes == \{([^}]*)\}/.exec(spec)?.[1];
  assert(declaredTypes !== undefined, "the generated spec declares no UserMessageTypes");
  const handlerCount = (declaredTypes ?? "")
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean).length;

  const estimate = estimateStateSpace(config as unknown as UnifiedVerificationConfig, analysis);
  assert(
    estimate.contextCount === contexts.length,
    `--estimate models ${estimate.contextCount} contexts; the .cfg declares ${contexts.length}`
  );
  assert(
    estimate.contexts.join(",") === emitted.join(","),
    `--estimate names {${estimate.contexts.join(", ")}}; the .cfg emits {${emitted.join(", ")}}`
  );
  assert(estimate.contextsDeclared, "a declared set was reported as the default");
  const n = contexts.length;
  assert(
    estimate.sendBranching === n * (2 ** n - 1) * tabs * handlerCount,
    `send branching ${estimate.sendBranching} does not match the quantifiers UserNext emits ` +
      `(${n} * ${2 ** n - 1} * ${tabs} * ${handlerCount})`
  );

  const specDir = writeSpecDir(spec, cfg, label);
  try {
    const result = await docker.runTLC(join(specDir, "UserApp.tla"), { workers: 1 });
    assert(
      result.success,
      `TLC failed on the spec for {${contexts.join(", ")}}: ${result.error ?? "see output"}`
    );

    const summary =
      /^(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue/m.exec(
        result.output
      );
    assert(summary?.[2] !== undefined, "TLC printed no summary line for a completed run");
    const distinct = Number.parseInt(summary?.[2] ?? "-1", 10);
    assert(
      result.stats?.distinctStates === distinct,
      `polly reported ${result.stats?.distinctStates} distinct states; TLC's summary says ${distinct}`
    );
    assert(
      estimate.estimatedStates <= distinct,
      `the estimate (${estimate.estimatedStates}) exceeds the ${distinct} states reached; ` +
        "it is documented as a lower bound"
    );

    ctx.log(
      `[e2e] Contexts = {${contexts.join(", ")}}: ${distinct} distinct states, ` +
        `depth ${result.stats?.searchDepth}, estimate ${estimate.estimatedStates}`
    );
    return { label, declared: contexts, distinct, depth: result.stats?.searchDepth };
  } finally {
    rmSync(specDir, { recursive: true, force: true });
  }
}

/**
 * Omitting the key must generate what it generated before polly#185, byte for
 * byte. The existing configs in the repo are the regression, so this is what
 * protects them.
 */
async function checkDefaultUnmoved(ctx: TierContext, analysis: CodebaseAnalysis): Promise<void> {
  const withoutKey = await generateTLA(configFor(), analysis);
  const withDefault = await generateTLA(configFor([...DEFAULT_CONTEXTS]), analysis);

  assert(
    cfgSetMembers(withoutKey.cfg, "Contexts").join(",") === DEFAULT_CONTEXTS.join(","),
    "a config with no `contexts` key no longer gets the browser-extension default"
  );
  assert(
    withoutKey.cfg === withDefault.cfg && withoutKey.spec === withDefault.spec,
    "declaring the default explicitly produces a different spec than omitting the key"
  );

  const estimate = estimateStateSpace(
    configFor() as unknown as UnifiedVerificationConfig,
    analysis
  );
  assert(!estimate.contextsDeclared, "the default set was reported as declared");
  assert(
    estimate.suggestions.some((s) => s.includes("no `contexts` key is declared")),
    "--estimate does not tell a consumer the set is the default"
  );
  ctx.log("[e2e] no `contexts` key: byte-identical to the pre-polly#185 output");
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const projectDir = mkdtempSync(join(tmpdir(), "polly-contexts-src-"));
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
    assert(
      analysis.handlers.length === 2,
      `expected 2 handlers from the fixture, analysed ${analysis.handlers.length}`
    );

    await checkDefaultUnmoved(ctx, analysis);

    const docker = new DockerRunner();
    const three = await measure(ctx, docker, analysis, [...DEFAULT_CONTEXTS]);
    const two = await measure(ctx, docker, analysis, ["background", "content"]);
    const one = await measure(ctx, docker, analysis, ["background"]);

    // Falsification: before polly#185 the declared set never reached the .cfg,
    // so all three runs were the same run. Agreement here means the key is not
    // being read and every assertion above proves nothing.
    assert(
      three.distinct !== two.distinct && two.distinct !== one.distinct,
      `the three declared sets reached the same state count ` +
        `(${three.distinct}, ${two.distinct}, ${one.distinct}); ` +
        "the `contexts` key is not reaching the .cfg — the polly#185 defect"
    );
    assert(
      three.distinct > two.distinct && two.distinct > one.distinct,
      `the state count does not fall with |Contexts| ` +
        `(${three.distinct}, ${two.distinct}, ${one.distinct})`
    );

    const reduction = three.distinct / one.distinct;
    assert(
      reduction > 50,
      `three contexts to one cut the model by only ${reduction.toFixed(1)}x; ` +
        "the ticket measured 105x on this shape"
    );

    ctx.log(
      `[e2e] three contexts to one: ${three.distinct} → ${one.distinct} distinct states ` +
        `(${reduction.toFixed(0)}x), depth ${three.depth} → ${one.depth}`
    );
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(projectDir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
