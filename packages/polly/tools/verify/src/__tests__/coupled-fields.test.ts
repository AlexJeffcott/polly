// polly#160 (A2): coupled-field write-coupling lint.

import { describe, expect, test } from "bun:test";
import { checkCoupledFields } from "../analysis/coupled-fields";
import type { MessageHandler } from "../types";

// Mirrors the builder in subsystem-verification.test.ts.
function makeHandler(messageType: string, fields: string[]): MessageHandler {
  return {
    messageType,
    node: "test",
    assignments: fields.map((field) => ({
      field,
      value: "true",
    })),
    preconditions: [],
    postconditions: [],
    constraints: [],
    context: "background",
    filePath: "test.ts",
    lineNumber: 1,
  };
}

const PAIR = ["authReady", "authenticated"];

describe("checkCoupledFields", () => {
  test("flags a handler that writes a non-empty strict subset (the #160 bug)", () => {
    const result = checkCoupledFields([PAIR], [makeHandler("register", ["authReady"])]);
    expect(result.valid).toBe(false);
    expect(result.violations).toHaveLength(1);
    const v = result.violations[0];
    expect(v?.handler).toBe("register");
    expect(v?.written).toEqual(["authReady"]);
    expect(v?.missing).toEqual(["authenticated"]);
    expect(new Set(v?.group)).toEqual(new Set(PAIR));
  });

  test("a handler writing the whole group is fine", () => {
    const result = checkCoupledFields(
      [PAIR],
      [makeHandler("connect", ["authReady", "authenticated"])]
    );
    expect(result.valid).toBe(true);
    expect(result.violations).toHaveLength(0);
  });

  test("a handler writing none of the group is fine", () => {
    const result = checkCoupledFields([PAIR], [makeHandler("ping", ["count"])]);
    expect(result.valid).toBe(true);
    expect(result.violations).toHaveLength(0);
  });

  test("a legitimate staged transition produces two violations — this is correct, not a checker bug; it is exactly why the lint WARNS rather than fails", () => {
    const result = checkCoupledFields(
      [PAIR],
      [makeHandler("connect", ["authenticated"]), makeHandler("flushQueue", ["authReady"])]
    );
    expect(result.violations).toHaveLength(2);
    expect(result.violations.map((v) => v.handler).sort()).toEqual(["connect", "flushQueue"]);
  });

  test("group membership is order-independent", () => {
    const result = checkCoupledFields(
      [PAIR],
      [makeHandler("connect", ["authenticated", "authReady"])]
    );
    expect(result.valid).toBe(true);
  });

  test("matches across dot/underscore field-name forms", () => {
    // group declared in underscore form, handler assigns dotted form.
    const result = checkCoupledFields(
      [["login_state_ready", "login_state_authed"]],
      [makeHandler("register", ["login.state.ready"])]
    );
    expect(result.valid).toBe(false);
    expect(result.violations[0]?.missing).toEqual(["login.state.authed"]);
  });

  test("a single-field group can never have a strict subset", () => {
    const result = checkCoupledFields([["solo"]], [makeHandler("h", ["solo"])]);
    expect(result.valid).toBe(true);
  });

  test("empty group and empty coupledFields are no-ops", () => {
    expect(checkCoupledFields([[]], [makeHandler("h", ["x"])]).valid).toBe(true);
    expect(checkCoupledFields([], [makeHandler("h", ["x"])]).valid).toBe(true);
  });
});
