// polly#160 (Ask #1): model-coverage report unit tests.

import { describe, expect, test } from "bun:test";
import {
  computeModelCoverage,
  type ModelCoverageReport,
  strictCoverageReasons,
} from "../analysis/model-coverage";
import type { OffSurfaceMutation } from "../core/model";
import type { MessageHandler } from "../types";

function offSurface(field: string, fn: string, signal = "session"): OffSurfaceMutation {
  return { field, signalVariable: signal, functionName: fn, filePath: "app.ts", line: 9 };
}

function makeHandler(
  messageType: string,
  fields: string[],
  opts: { ensures?: boolean } = {}
): MessageHandler {
  return {
    messageType,
    node: "test",
    assignments: fields.map((field) => ({ field, value: "true" })),
    preconditions: [],
    postconditions: opts.ensures ? [{ expression: "true", location: { line: 1, column: 0 } }] : [],
    location: { file: "test.ts", line: 1 },
  };
}

describe("computeModelCoverage", () => {
  test("reports which handlers write each declared field, in declaration order", () => {
    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      [
        makeHandler("connect", ["session.authenticated"]),
        makeHandler("authenticate", ["session.authenticated", "session.canSend"]),
      ]
    );
    expect(report.fieldCoverage).toEqual([
      { field: "session.authenticated", writers: ["authenticate", "connect"] },
      { field: "session.canSend", writers: ["authenticate"] },
    ]);
  });

  test("dedupes and sorts writers", () => {
    const report = computeModelCoverage(
      ["x"],
      [makeHandler("b", ["x"]), makeHandler("a", ["x"]), makeHandler("a", ["x"])]
    );
    expect(report.fieldCoverage[0]?.writers).toEqual(["a", "b"]);
  });

  test("flags a declared field no handler writes, and sets the strict violation", () => {
    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      [makeHandler("connect", ["session.authenticated"])]
    );
    expect(report.unwrittenFields).toEqual(["session.canSend"]);
    expect(report.hasStrictViolation).toBe(true);
  });

  test("no unwritten fields => no strict violation", () => {
    const report = computeModelCoverage(["a", "b"], [makeHandler("h", ["a", "b"])]);
    expect(report.unwrittenFields).toEqual([]);
    expect(report.hasStrictViolation).toBe(false);
  });

  test("matches underscore config keys against dotted assignment fields", () => {
    const report = computeModelCoverage(
      ["user_loggedIn"],
      [makeHandler("login", ["user.loggedIn"])]
    );
    expect(report.fieldCoverage[0]?.writers).toEqual(["login"]);
    expect(report.unwrittenFields).toEqual([]);
  });

  test("flags a handler that mutates declared state with no ensures()", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [makeHandler("register", ["session.canSend"], { ensures: false })]
    );
    expect(report.unconstrainedMutators).toHaveLength(1);
    expect(report.unconstrainedMutators[0]).toEqual({
      handler: "register",
      fields: ["session.canSend"],
      location: { file: "test.ts", line: 1 },
    });
  });

  test("a handler with an ensures() is not an unconstrained mutator", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [makeHandler("register", ["session.canSend"], { ensures: true })]
    );
    expect(report.unconstrainedMutators).toEqual([]);
  });

  test("ignores handler assignments to fields outside the declared schema", () => {
    // A handler mutating only scratch (non-modelled) state is not an
    // unconstrained mutator and contributes no writers.
    const report = computeModelCoverage(
      ["a"],
      [makeHandler("h", ["scratch.tmp"], { ensures: false })]
    );
    expect(report.unconstrainedMutators).toEqual([]);
    expect(report.unwrittenFields).toEqual(["a"]);
  });

  test("empty handler set => every declared field is unwritten", () => {
    const report = computeModelCoverage(["a", "b"], []);
    expect(report.unwrittenFields).toEqual(["a", "b"]);
    expect(report.hasStrictViolation).toBe(true);
  });

  test("no off-surface mutations => empty list, no strict violation from #163", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [makeHandler("h", ["session.canSend"])]
    );
    expect(report.offSurfaceMutations).toEqual([]);
    expect(report.hasStrictViolation).toBe(false);
  });
});

// polly#163: off-surface mutators folded into the coverage report.
describe("computeModelCoverage — off-surface mutators (polly#163)", () => {
  test("folds an off-surface writer into a declared field even when a handler also writes it", () => {
    const report = computeModelCoverage(
      ["session.authenticated", "session.canSend"],
      [makeHandler("AUTHENTICATE", ["session.authenticated", "session.canSend"])],
      [offSurface("session_canSend", "RecoveryFlow.register")]
    );
    // unwrittenFields cannot see this — AUTHENTICATE writes canSend — but #163 does.
    expect(report.unwrittenFields).toEqual([]);
    const canSend = report.fieldCoverage.find((f) => f.field === "session.canSend");
    expect(canSend?.writers).toEqual(["AUTHENTICATE"]);
    expect(canSend?.offSurfaceWriters).toEqual([
      { function: "RecoveryFlow.register", file: "app.ts", line: 9 },
    ]);
    expect(report.offSurfaceMutations).toHaveLength(1);
    expect(report.offSurfaceMutations[0]).toMatchObject({
      field: "session.canSend",
      function: "RecoveryFlow.register",
      declared: true,
    });
    expect(report.hasStrictViolation).toBe(true);
  });

  test("matches the off-surface underscore field against a dotted config key", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [],
      [offSurface("session_canSend", "register")]
    );
    expect(report.offSurfaceMutations[0]?.field).toBe("session.canSend");
  });

  test("drops off-surface writes to fields outside the declared schema (no noise)", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [makeHandler("h", ["session.canSend"])],
      [offSurface("settings_theme", "Options", "settings")]
    );
    expect(report.offSurfaceMutations).toEqual([]);
    expect(report.hasStrictViolation).toBe(false);
  });

  test("a field written ONLY off-surface is both unwritten and off-surface", () => {
    const report = computeModelCoverage(
      ["session.canSend"],
      [],
      [offSurface("session_canSend", "register")]
    );
    expect(report.unwrittenFields).toEqual(["session.canSend"]);
    expect(report.offSurfaceMutations).toHaveLength(1);
    expect(report.hasStrictViolation).toBe(true);
  });
});

function reportWith(overrides: Partial<ModelCoverageReport>): ModelCoverageReport {
  return {
    fieldCoverage: [],
    unwrittenFields: [],
    unconstrainedMutators: [],
    offSurfaceMutations: [],
    hasStrictViolation: false,
    ...overrides,
  };
}

describe("strictCoverageReasons", () => {
  test("clean report with no mesh findings => no reasons (strict passes)", () => {
    expect(strictCoverageReasons(reportWith({}), 0)).toEqual([]);
  });

  test("an unwritten field is a strict reason", () => {
    const reasons = strictCoverageReasons(
      reportWith({ unwrittenFields: ["session.authenticated"], hasStrictViolation: true }),
      0
    );
    expect(reasons).toHaveLength(1);
    expect(reasons[0]).toContain("1 declared state field");
  });

  test("unverified mesh/peer predicates are a strict reason", () => {
    const reasons = strictCoverageReasons(reportWith({}), 2);
    expect(reasons).toHaveLength(1);
    expect(reasons[0]).toContain("2 unverified");
  });

  test("both gaps produce both reasons", () => {
    const reasons = strictCoverageReasons(
      reportWith({ unwrittenFields: ["x"], hasStrictViolation: true }),
      1
    );
    expect(reasons).toHaveLength(2);
  });

  test("a declared off-surface mutation is a distinct strict reason (polly#163)", () => {
    const reasons = strictCoverageReasons(
      reportWith({
        offSurfaceMutations: [
          {
            field: "session.canSend",
            signalVariable: "session",
            function: "RecoveryFlow.register",
            file: "app.ts",
            line: 9,
            declared: true,
          },
        ],
        hasStrictViolation: true,
      }),
      0
    );
    expect(reasons).toHaveLength(1);
    expect(reasons[0]).toContain("outside any modelled transition");
  });
});
