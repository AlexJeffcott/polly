// polly#160: config validation for capabilities + coupledFields.

import { describe, expect, test } from "bun:test";
import { validateCapabilities, validateCoupledFields } from "../config/capability-validation";

const STATE = { authReady: { type: "boolean" }, authenticated: { type: "boolean" } } as Record<
  string,
  unknown
>;

describe("validateCapabilities", () => {
  test("a well-formed capability produces no issues", () => {
    const issues = validateCapabilities(
      [{ name: "canSend", enabledBy: "state.authReady", requires: "state.authenticated" }],
      STATE
    );
    expect(issues).toHaveLength(0);
  });

  test("G1: a bare-identifier expression (zero field refs) is a fatal error", () => {
    const issues = validateCapabilities(
      // "authReady" with no state./.value form extracts no refs and would
      // compile to a silently-vacuous invariant.
      [{ name: "canSend", enabledBy: "authReady", requires: "state.authenticated" }],
      STATE
    );
    const g1 = issues.find((i) => i.type === "capability_empty_expression");
    expect(g1?.severity).toBe("error");
    expect(g1?.field).toBe("capabilities.canSend.enabledBy");
  });

  test("G2: referencing a field not in state config is a fatal error", () => {
    const issues = validateCapabilities(
      [{ name: "canSend", enabledBy: "state.authReady", requires: "state.ghost" }],
      STATE
    );
    const g2 = issues.find((i) => i.type === "capability_unknown_field");
    expect(g2?.severity).toBe("error");
    expect(g2?.message).toContain("ghost");
  });

  test("an empty expression is a fatal error", () => {
    const issues = validateCapabilities(
      [{ name: "canSend", enabledBy: "", requires: "state.authenticated" }],
      STATE
    );
    expect(issues.some((i) => i.type === "capability_empty_expression")).toBe(true);
  });

  test("a missing name is reported", () => {
    const issues = validateCapabilities(
      [{ name: "  ", enabledBy: "state.authReady", requires: "state.authenticated" }],
      STATE
    );
    expect(issues.some((i) => i.type === "invalid_value")).toBe(true);
  });

  test("absent capabilities → no issues", () => {
    expect(validateCapabilities(undefined, STATE)).toHaveLength(0);
    expect(validateCapabilities([], STATE)).toHaveLength(0);
  });
});

describe("validateCoupledFields", () => {
  test("known fields → no issues", () => {
    expect(validateCoupledFields([["authReady", "authenticated"]], STATE)).toHaveLength(0);
  });

  test("an unknown field → fatal error naming it", () => {
    const issues = validateCoupledFields([["authReady", "ghostField"]], STATE);
    const err = issues.find((i) => i.type === "coupled_unknown_field");
    expect(err?.severity).toBe("error");
    expect(err?.message).toContain("ghostField");
    expect(err?.field).toBe("coupledFields[0]");
  });

  test("absent coupledFields → no issues", () => {
    expect(validateCoupledFields(undefined, STATE)).toHaveLength(0);
    expect(validateCoupledFields([], STATE)).toHaveLength(0);
  });
});
