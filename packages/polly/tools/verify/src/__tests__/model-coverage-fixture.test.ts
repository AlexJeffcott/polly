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
});
