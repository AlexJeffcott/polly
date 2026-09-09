import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis } from "../../../../analysis/src/types";
import { estimateStateSpace } from "../../analysis/state-space-estimator";
import { DEFAULT_CONTEXTS } from "../../codegen/model-constants";
import { generateSubsystemTLA, TLAGenerator } from "../../codegen/tla";
import { buildWitnessCfg } from "../../codegen/witness";
import type { UnifiedVerificationConfig } from "../../config/types";
import type { VerificationConfig } from "../../types";

/**
 * polly#185: `Contexts` is what the config declares, not three names fixed in
 * the writer.
 *
 * The set was `{background, content, popup}` for every project — chosen when
 * polly modelled a browser extension. Nothing a project declared changed it, so
 * a server paid `fieldProduct^3` for state replicated across two contexts it
 * did not have and `3 * 7` on every send for source/target pairs that could not
 * occur. Measured on a two-handler model at `maxInFlight: 1`, `maxTabs: 1`:
 * 38,464 distinct states at three contexts, 4,896 at two, 368 at one.
 *
 * The spec never names a member of the set — every use is a quantifier or a
 * function domain — so this one `.cfg` line decides the whole model.
 */

const STATE = {
  session: { type: "enum", values: ["anonymous", "pending", "authenticated"] },
} as unknown as VerificationConfig["state"];

function analysisWith(handlers: Array<{ messageType: string; node: string }>): CodebaseAnalysis {
  return {
    stateType: null,
    messageTypes: handlers.map((h) => h.messageType),
    fields: [],
    stateConstraints: [],
    handlers: handlers.map((h) => ({
      messageType: h.messageType,
      node: h.node,
      assignments: [],
      preconditions: [],
      postconditions: [],
      location: { file: `${h.node}/handlers.ts`, line: 1 },
    })),
  } as unknown as CodebaseAnalysis;
}

const ANALYSIS = analysisWith([
  { messageType: "AUTH_LOGIN", node: "server" },
  { messageType: "AUTH_LOGOUT", node: "server" },
]);

function configWith(extra: Record<string, unknown> = {}): VerificationConfig {
  return {
    state: STATE,
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
    ...extra,
  } as unknown as VerificationConfig;
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

describe("the emitted Contexts set", () => {
  test("a declared single context is the whole set", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ contexts: ["server"] }),
      ANALYSIS
    );

    expect(cfg).toContain("  Contexts = {server}");
    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["server"]);
  });

  test("a declared set is emitted in declaration order", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ contexts: ["server", "client", "worker"] }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["server", "client", "worker"]);
  });

  test("no `contexts` key keeps the browser-extension default", async () => {
    const { cfg } = await new TLAGenerator().generate(configWith(), ANALYSIS);

    expect(cfgSetMembers(cfg, "Contexts")).toEqual([...DEFAULT_CONTEXTS]);
  });

  test("adding the key and declaring the default changes neither .cfg nor .tla", async () => {
    const withoutKey = await new TLAGenerator().generate(configWith(), ANALYSIS);
    const withDefault = await new TLAGenerator().generate(
      configWith({ contexts: [...DEFAULT_CONTEXTS] }),
      ANALYSIS
    );

    expect(withDefault.cfg).toBe(withoutKey.cfg);
    expect(withDefault.spec).toBe(withoutKey.spec);
  });

  test("a name that is not a bare identifier is sanitised into a model value", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ contexts: ["main-window", "service:worker"] }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["main_window", "service_worker"]);
  });
});

describe("the declared set against the rest of the model", () => {
  test("the estimator's count and branching read off the same set", async () => {
    const config = configWith({ contexts: ["server"] });
    const { cfg } = await new TLAGenerator().generate(config, ANALYSIS);
    const estimate = estimateStateSpace(config as unknown as UnifiedVerificationConfig, ANALYSIS);

    expect(estimate.contextCount).toBe(1);
    expect(estimate.contexts).toEqual(cfgSetMembers(cfg, "Contexts"));
    expect(estimate.contextsDeclared).toBe(true);

    // |Contexts| * (2^|Contexts| - 1) * |Tabs| * handlers = 1 * 1 * 2 * 2.
    expect(estimate.sendBranching).toBe(4);
    expect(estimate.totalStateSpace).toBe(3);
  });

  test("the default set is reported as the default, and says so in a suggestion", () => {
    const estimate = estimateStateSpace(
      configWith() as unknown as UnifiedVerificationConfig,
      ANALYSIS
    );

    expect(estimate.contextsDeclared).toBe(false);
    expect(estimate.contexts).toEqual([...DEFAULT_CONTEXTS]);
    expect(estimate.suggestions.some((s) => s.includes("no `contexts` key is declared"))).toBe(
      true
    );
  });

  test("one context against three is the reduction the ticket measured", () => {
    const one = estimateStateSpace(
      configWith({ contexts: ["server"] }) as unknown as UnifiedVerificationConfig,
      ANALYSIS
    );
    const three = estimateStateSpace(
      configWith() as unknown as UnifiedVerificationConfig,
      ANALYSIS
    );

    // 3^3 * (3*7*2*2)^1 = 27 * 84 against 3^1 * (1*1*2*2)^1 = 3 * 4.
    expect(three.estimatedStates / one.estimatedStates).toBe(189);
  });

  test("the UserNext send quantifier is over the set, never over its members", async () => {
    const { spec } = await new TLAGenerator().generate(
      configWith({ contexts: ["server"] }),
      ANALYSIS
    );

    expect(spec).toContain(
      "\\/ \\E src \\in Contexts : \\E targetSet \\in (SUBSET Contexts \\ {{}}) : \\E tab \\in Tabs : \\E msgType \\in UserMessageTypes :"
    );
    // The spec names no context, so the .cfg line alone sizes the model.
    expect(spec).not.toContain("server");
  });

  test("ConnectPort and DisconnectPort still quantify over the single context", async () => {
    const { spec } = await new TLAGenerator().generate(
      configWith({ contexts: ["server"] }),
      ANALYSIS
    );

    expect(spec).toContain("\\/ \\E c \\in Contexts : ConnectPort(c)");
    expect(spec).toContain("\\/ \\E c \\in Contexts : DisconnectPort(c)");
  });

  test("tabSymmetry is unaffected by the declared set", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({
        contexts: ["server", "client"],
        messages: { maxInFlight: 1, maxTabs: 1, tabSymmetry: true },
      }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["server", "client"]);
    expect(cfgSetMembers(cfg, "Tabs")).toEqual(["Tab0", "Tab1"]);
    expect(cfg).toContain("SYMMETRY");
  });
});

describe("contexts are global to the spec, not per subsystem", () => {
  test("every generated subsystem spec gets the declared set", async () => {
    const config = configWith({
      contexts: ["server", "client"],
      subsystems: {
        auth: { state: ["session"], handlers: ["AUTH_LOGIN", "AUTH_LOGOUT"] },
      },
    });

    const { cfg } = await generateSubsystemTLA(
      "auth",
      { state: ["session"], handlers: ["AUTH_LOGIN", "AUTH_LOGOUT"] },
      config,
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["server", "client"]);
  });
});

describe("mesh under a single context", () => {
  const meshConfig = configWith({
    contexts: ["server"],
    mesh: { todos: { entries: { type: "enum", values: ["empty", "one"] } } },
  });

  test("PropagateMeshOp is emitted but requires two distinct contexts", async () => {
    const { spec } = await new TLAGenerator().generate(meshConfig, ANALYSIS);

    expect(spec).toContain("PropagateMeshOp(src, dst, docId) ==");
    // `src # dst` is unsatisfiable over a one-element set, so the action is
    // never enabled and the Automerge sync the mesh block declares is not
    // modelled. The config validator warns; the codegen is unchanged.
    expect(spec).toContain("/\\ src # dst");
    expect(spec).toContain(
      "\\/ \\E src, dst \\in Contexts : \\E docId \\in MeshDocs : PropagateMeshOp(src, dst, docId)"
    );
  });

  test("two contexts leave the mesh action reachable", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({
        contexts: ["peerA", "peerB"],
        mesh: { todos: { entries: { type: "enum", values: ["empty", "one"] } } },
      }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual(["peerA", "peerB"]);
  });
});

describe("the dead maxContexts key", () => {
  test("messages.maxContexts emits no constant", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ messages: { maxInFlight: 1, maxContexts: 4 } }),
      ANALYSIS
    );

    expect(cfg).not.toContain("MaxContexts");
  });

  test("messages.maxContexts still narrows the default Tabs set", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ messages: { maxInFlight: 1, maxContexts: 4 } }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Tabs")).toEqual(["0"]);
  });

  test("messages.maxContexts does not size Contexts", async () => {
    const { cfg } = await new TLAGenerator().generate(
      configWith({ messages: { maxInFlight: 1, maxContexts: 4 } }),
      ANALYSIS
    );

    expect(cfgSetMembers(cfg, "Contexts")).toEqual([...DEFAULT_CONTEXTS]);
  });
});

describe("a hand-written spec is untouched by the key", () => {
  test("customTLAPaths: the witness cfg carries the author's constants, not polly's", () => {
    // A hand-written spec declares its own constants and has no `Contexts` at
    // all. `buildWitnessCfg` copies the CONSTANTS block verbatim, so declaring
    // `contexts` in the polly config cannot reach it.
    const handWritten = [
      "SPECIFICATION Spec",
      "",
      "CONSTANT Controller = safe",
      "",
      "INVARIANTS",
      "  TypeOK",
      "",
    ].join("\n");

    const witnessCfg = buildWitnessCfg(handWritten);

    expect(witnessCfg).toContain("Controller = safe");
    expect(witnessCfg).not.toContain("Contexts");
    expect(witnessCfg).not.toContain("background");
  });
});
