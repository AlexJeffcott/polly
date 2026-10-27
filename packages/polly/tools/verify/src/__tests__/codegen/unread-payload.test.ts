import { describe, expect, test } from "bun:test";
import { collapseUnreadPayload } from "../../codegen/tla";

/**
 * The router picks a fresh payload from `PayloadType` on every delivery. When
 * no expression reads a payload field, each value is a successor nothing
 * checks: examples/mesh-recovery-pair went 18,579,064 -> 2,322,340 distinct
 * states with the 8-record type narrowed to one.
 */

const DECL = "PayloadType == [id: Value, text: Value]";

function spec(body: string): string {
  return `---- MODULE UserApp ----\n${DECL}\n\nHandleX(ctx) ==\n${body}\n====\n`;
}

describe("collapseUnreadPayload", () => {
  test("no payload read: PayloadType becomes one record of the same type", () => {
    const out = collapseUnreadPayload(
      spec("  /\\ contextStates' = [contextStates EXCEPT ![ctx].a = TRUE]")
    );
    expect(out).toContain("PayloadType == {CHOOSE p \\in [id: Value, text: Value] : TRUE}");
    expect(out).not.toContain(`${DECL}\n`);
  });

  test("a guard reads payload: unchanged", () => {
    const s = spec('  /\\ payload.text # ""');
    expect(collapseUnreadPayload(s)).toBe(s);
  });

  test("an ensures reads the post-state payload: unchanged", () => {
    const s = spec("  /\\ contextStates'[ctx].a = payload'.text");
    expect(collapseUnreadPayload(s)).toBe(s);
  });

  test("the declaration and `payload \\in PayloadType` alone do not count as reads", () => {
    const s = `${spec("  /\\ UNCHANGED contextStates")}\nUserInit == payload \\in PayloadType\n`;
    expect(collapseUnreadPayload(s)).toContain("CHOOSE p");
  });
});
