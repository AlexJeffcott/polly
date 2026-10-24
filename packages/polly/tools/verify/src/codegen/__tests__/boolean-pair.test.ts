// The `[false, true]` boolean shorthand of FieldConfig (examples/full-featured
// uses it). It was untyped, and the codegen treated it as a leaf field only
// because `"values" in` is true for any array, through Array.prototype.values.

import { describe, expect, test } from "bun:test";
import { type CodebaseAnalysis, isBooleanPair, type VerificationConfig } from "../../types";
import { generateTLA } from "../tla";

// No analysed fields, so every field in the spec comes from the config.
const analysis: CodebaseAnalysis = {
  stateType: null,
  messageTypes: [],
  fields: [],
  handlers: [],
  stateConstraints: [],
};

function configWith(state: VerificationConfig["state"]): VerificationConfig {
  return {
    state,
    messages: { maxInFlight: 1, maxTabs: 1 },
    onBuild: "warn",
    onRelease: "warn",
  };
}

describe("boolean pair state field", () => {
  test("[false, true] is a BOOLEAN field that starts FALSE", async () => {
    const { spec, cfg } = await generateTLA(configWith({ flag: [false, true] }), analysis);

    expect(spec).toContain("flag: BOOLEAN");
    expect(spec).toContain("flag |-> FALSE");
    expect(cfg).not.toContain("Flag_");
  });

  test("the first element is the initial value", async () => {
    const { spec } = await generateTLA(configWith({ flag: [true, false] }), analysis);

    expect(spec).toContain("flag: BOOLEAN");
    expect(spec).toContain("flag |-> TRUE");
  });

  test("a nested pair flattens to parent_child", async () => {
    const { spec } = await generateTLA(
      configWith({ session: { active: [false, true] } }),
      analysis
    );

    expect(spec).toContain("session_active: BOOLEAN");
    expect(spec).toContain("session_active |-> FALSE");
  });
});

describe("isBooleanPair", () => {
  test("accepts two booleans", () => {
    expect(isBooleanPair([false, true])).toBe(true);
    expect(isBooleanPair([true, true])).toBe(true);
  });

  test("rejects other shapes", () => {
    expect(isBooleanPair({ type: "boolean" })).toBe(false);
    expect(isBooleanPair({ values: ["a", "b"] })).toBe(false);
    expect(isBooleanPair({ nested: [false, true] })).toBe(false);
  });
});
