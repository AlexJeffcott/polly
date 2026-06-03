// polly#160 (A3): capability declarations desugar into TLA+ safety invariants.
//
// These pin the generated spec/cfg syntax. The end-to-end check that a real TLC
// run reports the counterexample lives in scripts/e2e-capabilities-guard.ts.

import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import { TLAGenerator } from "../tla";

function baseConfig(): VerificationConfig {
  return {
    state: {
      authReady: { type: "boolean" },
      authenticated: { type: "boolean" },
    },
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "error",
  };
}

const baseAnalysis: CodebaseAnalysis = {
  stateType: null,
  messageTypes: ["test"],
  fields: [],
  handlers: [],
  stateConstraints: [],
};

describe("capabilities desugar to TLA+ invariants (issue #160)", () => {
  test("a capability emits a safety invariant and an INVARIANTS cfg entry", async () => {
    const config = baseConfig();
    config.capabilities = [
      { name: "canSend", enabledBy: "state.authReady", requires: "state.authenticated" },
    ];

    const { spec, cfg } = await new TLAGenerator().generate(config, baseAnalysis);

    // The invariant is defined in the spec body...
    expect(spec).toContain("Capability_canSend ==");
    // ...as the material implication (!(enabledBy)) || (requires), i.e.
    // enabledBy => requires — the enabledBy side is negated, the requires side
    // is positive (a wrong direction would fail these).
    expect(spec).toContain("~(contextStates[ctx].authReady)");
    expect(spec).toContain("\\/ (contextStates[ctx].authenticated)");
    // ...and listed in the .cfg INVARIANTS clause so TLC actually checks it.
    expect(cfg).toContain("INVARIANTS");
    expect(cfg).toContain("Capability_canSend");
  });

  test("the message becomes the invariant comment", async () => {
    const config = baseConfig();
    config.capabilities = [
      {
        name: "canSend",
        enabledBy: "state.authReady",
        requires: "state.authenticated",
        message: "sends require an authenticated session",
      },
    ];

    const { spec } = await new TLAGenerator().generate(config, baseAnalysis);
    expect(spec).toContain("sends require an authenticated session");
  });

  test("no capabilities → no Capability_ invariant", async () => {
    const { spec, cfg } = await new TLAGenerator().generate(baseConfig(), baseAnalysis);
    expect(spec).not.toContain("Capability_");
    expect(cfg).not.toContain("INVARIANT Capability_");
  });
});
