// polly#160 (Ask #1) end-to-end (no Docker): drive the REAL analyzeCodebase
// pipeline against the capability-guard fixture and read model coverage off the
// extracted handlers. Proves the report works through the documented entry
// point, not a hand-built handler list.
//
// Fixture shape (src/background/index.ts):
//   AUTHENTICATE -> writes session.authenticated AND session.canSend
//   REGISTER     -> writes session.canSend only (the bug)
// Neither handler declares an ensures().

import { describe, expect, test } from "bun:test";
import path from "node:path";
import { analyzeCodebase } from "../../../analysis/src";
import { computeModelCoverage, strictCoverageReasons } from "../analysis/model-coverage";

const projectPath = path.join(__dirname, "../../test-projects/capability-guard");
const strictFixturePath = path.join(__dirname, "../../test-projects/coverage-strict");
const offSurfacePath = path.join(__dirname, "../../test-projects/coverage-offsurface");

describe("model coverage on the capability-guard fixture (polly#160)", () => {
  test("reports the uneven write distribution the scattered invariant produces", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });

    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      analysis.handlers
    );

    const byField = Object.fromEntries(report.fieldCoverage.map((f) => [f.field, f.writers]));
    // authenticated is written by only the correct path; canSend by both —
    // the "written by some paths but not others" signal.
    expect(byField["session.authenticated"]).toEqual(["AUTHENTICATE"]);
    expect(byField["session.canSend"]).toEqual(["AUTHENTICATE", "REGISTER"]);
  });

  test("the coverage-strict fixture: a declared field no handler writes fails strict", async () => {
    // Purpose-built fixture: declares session.authenticated + session.canSend
    // but the only handler (OPEN_GATE) writes canSend, leaving authenticated
    // with no modelled mutating path — the omission class.
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(strictFixturePath, "tsconfig.json"),
    });

    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      analysis.handlers
    );

    expect(report.unwrittenFields).toEqual(["session.authenticated"]);
    expect(report.hasStrictViolation).toBe(true);
    // The CLI's --strict gate would fail on exactly this.
    expect(strictCoverageReasons(report, 0)).toHaveLength(1);
  });

  test("both fixture handlers are unconstrained mutators (no ensures())", async () => {
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });

    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      analysis.handlers
    );

    const flagged = report.unconstrainedMutators.map((m) => m.handler).sort();
    expect(flagged).toEqual(["AUTHENTICATE", "REGISTER"]);
  });

  test("a dispatched-handler write is on-surface — no off-surface false positive", async () => {
    // Both capability-guard writes go through bus.on(...) handlers, so the
    // off-surface scan must report nothing.
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(projectPath, "tsconfig.json"),
    });
    expect(analysis.offSurfaceMutations).toEqual([]);
  });
});

describe("off-surface mutator on the coverage-offsurface fixture (polly#163)", () => {
  test("reports a non-dispatched method mutation the model never explores", async () => {
    // Fixture: AUTHENTICATE (dispatched) writes session.canSend AND
    // RecoveryFlow.register (a plain method) also writes session.canSend.
    const analysis = await analyzeCodebase({
      tsConfigPath: path.join(offSurfacePath, "tsconfig.json"),
    });

    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      analysis.handlers,
      analysis.offSurfaceMutations ?? []
    );

    // canSend has a handler writer, so #160's unwrittenFields cannot flag it...
    expect(report.unwrittenFields).toEqual([]);
    // ...but #163 surfaces the non-dispatched writer.
    expect(report.offSurfaceMutations).toHaveLength(1);
    expect(report.offSurfaceMutations[0]).toMatchObject({
      field: "session.canSend",
      function: "RecoveryFlow.register",
      declared: true,
    });

    const canSend = report.fieldCoverage.find((f) => f.field === "session.canSend");
    expect(canSend?.writers).toEqual(["AUTHENTICATE"]);
    expect(canSend?.offSurfaceWriters?.[0]?.function).toBe("RecoveryFlow.register");

    // The CLI's --strict gate would fail closed on exactly this.
    expect(report.hasStrictViolation).toBe(true);
    expect(strictCoverageReasons(report, 0)).toHaveLength(1);
  });
});
