// polly#168: a description with an embedded newline used to emit only its first
// line with a `\*` marker; every line after it landed in the module as bare
// prose and SANY rejected the module. This reaches production through a
// capability's `message` (tla.ts addCapabilityInvariants), so it was a live
// defect, not one gated behind the dead JSDoc path.

import { expect, describe as group, test } from "bun:test";
import { describe } from "../invariants";
import { TemporalTLAGenerator } from "../temporal";

group("describe() renders every line as a TLA+ comment (polly#168)", () => {
  test("a single line gets one marker", () => {
    expect(describe("one line")).toEqual(["\\* one line"]);
  });

  test("every line of a multi-line description gets its own marker", () => {
    expect(describe("first\nsecond\nthird")).toEqual(["\\* first", "\\* second", "\\* third"]);
  });

  test("an absent or blank description renders nothing", () => {
    expect(describe(undefined)).toEqual([]);
    expect(describe("")).toEqual([]);
    expect(describe("   \n  ")).toEqual([]);
  });
});

group("temporal properties carry the same fix", () => {
  test("a multi-line property description leaves no unmarked line", () => {
    const [rendered] = new TemporalTLAGenerator().generateTLAProperties([
      {
        name: "SomeProperty",
        description: "why this holds\nand the second line",
        type: "always",
        target: "TRUE",
      },
    ]);

    const commentLines = rendered!.split("\n").slice(0, 2);
    expect(commentLines).toEqual(["\\* why this holds", "\\* and the second line"]);
  });
});
