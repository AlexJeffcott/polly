// polly#160 end-to-end (no Docker): drive the REAL analyzeCodebase → generateTLA
// pipeline against the capability-guard fixture, where REGISTER grants `canSend`
// without `authenticated`. Proves the feature works through the documented entry
// point, not a hand-wired config. The TLC counterexample verdict itself needs
// Docker and lives in scripts/e2e-capabilities-guard.ts.

import { describe, expect, test } from "bun:test";
import path from "node:path";
import { analyzeCodebase } from "../../../analysis/src";
import { checkCoupledFields } from "../analysis/coupled-fields";
import { generateTLA } from "../codegen/tla";
import type { VerificationConfig } from "../types";

const projectPath = path.join(__dirname, "../../test-projects/capability-guard");

// The fixture's verification.config.ts, inlined (generateTLA takes the config
// object directly; the CLI's loader is not on this path).
const config = {
  state: {
    "session.authenticated": { type: "boolean" },
    "session.canSend": { type: "boolean" },
  },
  capabilities: [
    {
      name: "canSend",
      enabledBy: "session.value.canSend",
      requires: "session.value.authenticated",
      message: "sends require an authenticated session",
    },
  ],
  coupledFields: [["session.authenticated", "session.canSend"]],
  messages: { maxInFlight: 1, maxTabs: 1 },
  onBuild: "warn" as const,
  onRelease: "error" as const,
} satisfies VerificationConfig;

describe("capability-guard fixture (polly#160)", () => {
  test("the capability invariant is generated against the analyzed state fields", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });

    const { spec, cfg } = await generateTLA(config, analysis);

    // The desugared invariant references the SAME sanitized field names the
    // State record declares (proving the tsExpressionToTLA reuse).
    expect(spec).toContain("Capability_canSend ==");
    expect(spec).toContain("~(contextStates[ctx].session_canSend)");
    expect(spec).toContain("\\/ (contextStates[ctx].session_authenticated)");
    expect(cfg).toContain("Capability_canSend");
  });

  test("the coupled-field lint flags REGISTER (grants canSend, not authenticated) but not AUTHENTICATE", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });

    const result = checkCoupledFields(config.coupledFields, analysis.handlers);
    const flagged = result.violations.map((v) => v.handler);

    expect(flagged).toContain("REGISTER");
    expect(flagged).not.toContain("AUTHENTICATE");
  });
});
