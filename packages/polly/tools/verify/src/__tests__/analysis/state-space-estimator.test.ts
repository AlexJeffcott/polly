import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../../analysis/src/types";
import { estimateStateSpace, estimateSubsystems } from "../../analysis/state-space-estimator";
import { TLAGenerator } from "../../codegen/tla";
import type { UnifiedVerificationConfig } from "../../config/types";
import type { VerificationConfig } from "../../types";

/**
 * polly#183: what `--estimate` predicts against what the generator emits.
 *
 * The estimator modelled `maxTabs + 1` contexts while the `.cfg` writer emitted
 * a fixed three, and it left out the send branching entirely. On eal's `auth`
 * subsystem it said ~5,832 states for a model that reached 9.6M distinct states
 * in three minutes, was still at depth 6 with 8M queued, and never terminated.
 * The figure did not move when the subsystem was resized to the shape that
 * finishes in a second, because neither handler count nor maxInFlight entered
 * it in a way that reflected the spec.
 */

/** eal's `auth`: two 3-valued fields, so `fieldProduct` = 9. */
const AUTH_STATE = {
  session: { type: "enum", values: ["anonymous", "pending", "authenticated"] },
  token: { type: "enum", values: ["none", "fresh", "expired"] },
};

function analysisWithHandlers(count: number): CodebaseAnalysis {
  const messageTypes = Array.from({ length: count }, (_, i) => `AUTH_${i}`);
  return {
    stateType: null,
    messageTypes,
    fields: [],
    stateConstraints: [],
    handlers: messageTypes.map((messageType) => ({
      messageType,
      node: "background",
      assignments: [],
      preconditions: [],
      postconditions: [],
      location: { file: "auth.ts", line: 1 },
    })),
  } as unknown as CodebaseAnalysis;
}

function authConfig(maxInFlight: number): UnifiedVerificationConfig {
  return {
    state: AUTH_STATE,
    messages: { maxInFlight, maxTabs: null },
    onBuild: "warn",
    onRelease: "error",
  } as unknown as UnifiedVerificationConfig;
}

describe("estimateStateSpace — the eal auth subsystem", () => {
  test("9 handlers at maxInFlight 2 is called infeasible, in the order the run reached", () => {
    const estimate = estimateStateSpace(authConfig(2), analysisWithHandlers(9));

    // Observed: 9.6M distinct states and rising, 8M queued, killed at ~5 min.
    // The old formula said ~5,832 — trivially feasible.
    expect(estimate.estimatedStates).toBeGreaterThan(1e8);
    expect(estimate.feasibility).toBe("infeasible");
  });

  test("7 handlers at maxInFlight 1 is called feasible, in the order it measured", () => {
    const estimate = estimateStateSpace(authConfig(1), analysisWithHandlers(7));

    // Measured: 97,600 distinct states, queue 0, depth 9, one second.
    expect(estimate.estimatedStates).toBeGreaterThan(1e4);
    expect(estimate.estimatedStates).toBeLessThan(1e6);
    expect(estimate.feasibility).toBe("feasible");
  });

  test("resizing the subsystem moves the estimate", () => {
    // The defect in one line: the two configurations above both estimated
    // ~5,832, because neither lever entered the formula.
    const before = estimateStateSpace(authConfig(2), analysisWithHandlers(9)).estimatedStates;
    const after = estimateStateSpace(authConfig(1), analysisWithHandlers(7)).estimatedStates;

    expect(before).toBeGreaterThan(after * 100);
  });

  test("the send branching is in the estimate at all", () => {
    const estimate = estimateStateSpace(authConfig(1), analysisWithHandlers(7));

    // |Contexts| x (2^|Contexts| - 1) x |Tabs| x handlers = 3 x 7 x 2 x 7.
    expect(estimate.sendBranching).toBe(294);
    expect(estimate.interleavingFactor).toBe(294);
  });

  test("the context count is the generated one, not maxTabs + 1", () => {
    const estimate = estimateStateSpace(authConfig(1), analysisWithHandlers(7));

    expect(estimate.contextCount).toBe(3);
    expect(estimate.totalStateSpace).toBe(9 ** 3);
  });

  test("the figure is reported as a lower bound, naming what it omits", () => {
    const estimate = estimateStateSpace(authConfig(1), analysisWithHandlers(7));

    expect(estimate.warnings.some((w) => w.includes("deliveredTo"))).toBe(true);
  });

  test("the suggestions name the term that dominates this estimate", () => {
    const estimate = estimateStateSpace(authConfig(2), analysisWithHandlers(9));

    expect(estimate.suggestions.some((s) => s.startsWith("Dominant term:"))).toBe(true);
    expect(estimate.suggestions.some((s) => s.includes("maxInFlight 2 → 1"))).toBe(true);
  });
});

describe("estimateSubsystems", () => {
  const config = {
    state: {
      ...AUTH_STATE,
      paired: { type: "boolean" },
    },
    messages: { maxInFlight: 2, maxTabs: null },
    onBuild: "warn",
    onRelease: "error",
    subsystems: {
      auth: { state: ["session", "token"], handlers: ["AUTH_0", "AUTH_1"] },
      pairing: { state: ["paired"], handlers: ["PAIR_0"], bounds: { maxInFlight: 1 } },
    },
  } as unknown as UnifiedVerificationConfig;

  test("estimates the models that will actually run, one per subsystem", () => {
    const estimates = estimateSubsystems(config);

    expect(estimates.map((e) => e.subsystem)).toEqual(["auth", "pairing"]);
  });

  test("a subsystem sees only its own state fields", () => {
    const [auth, pairing] = estimateSubsystems(config);

    expect(auth?.fieldProduct).toBe(9);
    expect(pairing?.fieldProduct).toBe(2);
  });

  test("bounds.maxInFlight overrides the top-level messages.maxInFlight", () => {
    const [auth, pairing] = estimateSubsystems(config);

    expect(auth?.maxInFlight).toBe(2);
    expect(pairing?.maxInFlight).toBe(1);
  });

  test("a config with no subsystems estimates nothing per subsystem", () => {
    expect(estimateSubsystems(authConfig(1))).toEqual([]);
  });
});

/**
 * The pin that stops the two drifting again: the estimator's quantities read
 * against the `.cfg` and `.tla` the generator produces for the same config.
 */
describe("estimator against the generated spec", () => {
  async function generateFor(config: VerificationConfig, analysis: CodebaseAnalysis) {
    return new TLAGenerator().generate(config, analysis);
  }

  /** Members of a `Name = {a, b, c}` assignment in a `.cfg`. */
  function cfgSetMembers(cfg: string, name: string): string[] {
    const match = new RegExp(`^\\s*${name} = \\{([^}]*)\\}`, "m").exec(cfg);
    if (!match?.[1]) throw new Error(`no ${name} assignment in cfg`);
    return match[1]
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);
  }

  test.each([
    ["default tabs", { maxInFlight: 1, maxTabs: null }, undefined],
    ["explicit maxTabs", { maxInFlight: 2, maxTabs: 2 }, undefined],
    ["tab symmetry", { maxInFlight: 1, maxTabs: 1, tabSymmetry: true }, undefined],
    ["project constant", { maxInFlight: 1, maxTabs: null, maxWorkers: 2 }, undefined],
    // polly#185: the declared set has to move both sides together.
    ["one declared context", { maxInFlight: 1, maxTabs: null }, ["server"]],
    ["two declared contexts", { maxInFlight: 1, maxTabs: 1 }, ["server", "client"]],
    ["four declared contexts", { maxInFlight: 1, maxTabs: null }, ["a", "b", "c", "d"]],
  ])("%s: contexts and tabs match the .cfg the generator writes", async (_label, messages, contexts) => {
    const config = {
      state: AUTH_STATE,
      ...(contexts ? { contexts } : {}),
      messages,
      onBuild: "warn",
      onRelease: "error",
    } as unknown as VerificationConfig;
    const analysis = analysisWithHandlers(4);

    const { cfg } = await generateFor(config, analysis);
    const estimate = estimateStateSpace(config as unknown as UnifiedVerificationConfig, analysis);

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(estimate.contexts);
    expect(cfgSetMembers(cfg, "Contexts")).toHaveLength(estimate.contextCount);
    expect(cfgSetMembers(cfg, "Tabs")).toHaveLength(estimate.tabCount);
  });

  test.each([
    ["the default set", undefined],
    ["a declared set", ["server", "client"]],
    ["a single declared context", ["server"]],
  ])("%s: the branching factor matches the quantifiers UserNext emits", async (_l, contexts) => {
    const config = {
      state: AUTH_STATE,
      ...(contexts ? { contexts } : {}),
      messages: { maxInFlight: 1, maxTabs: null },
      onBuild: "warn",
      onRelease: "error",
    } as unknown as VerificationConfig;
    const analysis = analysisWithHandlers(4);

    const { spec, cfg } = await generateFor(config, analysis);
    const estimate = estimateStateSpace(config as unknown as UnifiedVerificationConfig, analysis);

    // The send step the estimator is modelling.
    expect(spec).toContain(
      "\\/ \\E src \\in Contexts : \\E targetSet \\in (SUBSET Contexts \\ {{}}) : \\E tab \\in Tabs : \\E msgType \\in UserMessageTypes :"
    );

    const contextCount = cfgSetMembers(cfg, "Contexts").length;
    const tabs = cfgSetMembers(cfg, "Tabs").length;
    const declared = /UserMessageTypes == \{([^}]*)\}/.exec(spec)?.[1];
    if (declared === undefined) throw new Error("the generated spec declares no UserMessageTypes");
    const messageTypes = declared
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);

    expect(estimate.sendBranching).toBe(
      contextCount * (2 ** contextCount - 1) * tabs * messageTypes.length
    );
  });
});
