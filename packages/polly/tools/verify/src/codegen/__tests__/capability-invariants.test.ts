// polly#160 (A3): capability declarations desugar into TLA+ safety invariants.
//
// These pin the generated spec/cfg syntax. The end-to-end check that a real TLC
// run reports the counterexample lives in scripts/e2e-capabilities-guard.ts.

import { describe, expect, test } from "bun:test";
import type { CodebaseAnalysis, VerificationConfig } from "../../types";
import {
  capabilityFitsSubsystem,
  capabilityStateRefs,
  generateSubsystemTLA,
  TLAGenerator,
} from "../tla";

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

describe("capabilities are scoped per subsystem (issue #196)", () => {
  const cap = {
    name: "SyncStateEquals",
    enabledBy: "offlineQueueState.value.syncState === 'synced'",
    requires: "offlineQueueState.value.unsyncedChanges === 0",
  };

  test("reads signal fields, whole signals and state paths", () => {
    expect(capabilityStateRefs(cap).sort()).toEqual([
      "offlineQueueState.syncState",
      "offlineQueueState.unsyncedChanges",
    ]);
    expect(
      capabilityStateRefs({ name: "c", enabledBy: "todos.value.length > 0", requires: "state.a.b" })
    ).toEqual(["todos.length", "a.b"]);
    expect(capabilityStateRefs({ name: "c", enabledBy: "user.value", requires: "true" })).toEqual([
      "user",
    ]);
  });

  test("kept only where the subsystem owns every field it reads", () => {
    const owner = ["offlineQueueState.syncState", "offlineQueueState.unsyncedChanges"];
    expect(capabilityFitsSubsystem(cap, owner)).toBe(true);
    expect(capabilityFitsSubsystem(cap, ["appState.appPhase"])).toBe(false);
    expect(capabilityFitsSubsystem(cap, ["offlineQueueState.syncState"])).toBe(false);
    // A whole-signal field covers paths inside it.
    expect(capabilityFitsSubsystem(cap, ["offlineQueueState"])).toBe(true);
  });

  test("a capability that reads no recognisable field is kept", () => {
    expect(capabilityFitsSubsystem({ name: "c", enabledBy: "true", requires: "typo" }, [])).toBe(
      true
    );
  });

  test("generateSubsystemTLA emits the invariant only in the owning subsystem", async () => {
    const config: VerificationConfig = {
      state: {
        "appState.appPhase": { type: "enum", values: ["idle", "busy"] },
        "offlineQueueState.syncState": { type: "enum", values: ["synced", "pending"] },
        "offlineQueueState.unsyncedChanges": { type: "number", min: 0, max: 2 },
      },
      messages: { maxInFlight: 1, maxTabs: 1 },
      capabilities: [cap],
      onBuild: "warn",
      onRelease: "error",
    };
    const app = await generateSubsystemTLA(
      "app",
      { state: ["appState.appPhase"], handlers: ["test"] },
      config,
      baseAnalysis
    );
    expect(app.spec).not.toContain("Capability_SyncStateEquals");
    expect(app.spec).not.toContain("offlineQueueState_syncState");

    const queue = await generateSubsystemTLA(
      "offlineQueue",
      {
        state: ["offlineQueueState.syncState", "offlineQueueState.unsyncedChanges"],
        handlers: ["test"],
      },
      config,
      baseAnalysis
    );
    expect(queue.spec).toContain("Capability_SyncStateEquals ==");
    expect(queue.cfg).toContain("Capability_SyncStateEquals");
  });
});
