import { describe, expect, test } from "bun:test";
import * as path from "node:path";
import {
  handlerEffectLines,
  neverTaken,
  parseHandlerCoverage,
} from "../../runner/handler-coverage";

/**
 * A handler whose requires guards never all hold is never taken, and every
 * ensures on it passes unchecked. The fixtures are TLC 2.19 `-coverage`
 * transcripts from the polly-tla image, with the generated spec each was run on.
 */

const FIXTURES = path.join(import.meta.dir, "fixtures", "handler-coverage");

async function fixture(name: string): Promise<{ spec: string; output: string }> {
  return {
    spec: await Bun.file(path.join(FIXTURES, `${name}.tla`)).text(),
    output: await Bun.file(path.join(FIXTURES, `${name}.tlc.log`)).text(),
  };
}

const SPEC = `---- MODULE UserApp ----
UserMessageTypes == {"PING", "TOGGLE"}

HandlePing(ctx) ==
  /\\ contextStates[ctx].active = TRUE \\* must be active
  /\\ contextStates' = [contextStates EXCEPT ![ctx].count = @ + 1]

HandleToggle(ctx) ==
  /\\ \\E i \\in 1..Len(contextStates[ctx].items) :
    /\\ contextStates' = [contextStates EXCEPT ![ctx].items[i] = TRUE]

HandleIdle(ctx) ==
  \\* No state changes in handler
  /\\ UNCHANGED contextStates

StateTransition(ctx, msgType) ==
  IF msgType = "PING" THEN HandlePing(ctx)
  ELSE IF msgType = "TOGGLE" THEN HandleToggle(ctx)
  ELSE IF msgType = "IDLE" THEN HandleIdle(ctx)
  ELSE FALSE
====
`;

describe("handlerEffectLines", () => {
  test("reads the last top-level conjunct, not one nested in an \\E", () => {
    expect([...handlerEffectLines(SPEC)]).toEqual([
      ["HandlePing", 6],
      ["HandleToggle", 9],
      ["HandleIdle", 14],
    ]);
  });
});

describe("parseHandlerCoverage", () => {
  test("undefined when the output has no coverage block", () => {
    const output = "8 states generated, 8 distinct states found, 0 states left on queue.\n";
    expect(parseHandlerCoverage(SPEC, "UserApp", output)).toBeUndefined();
  });

  test("a guard evaluated but its effect never: the handler is never taken", () => {
    const output = `The coverage statistics at 2026-10-27 10:00:39
  line 5, col 6 to line 5, col 38 of module UserApp: 4096
  line 6, col 6 to line 6, col 66 of module UserApp: 0
  line 9, col 6 to line 9, col 50 of module UserApp: 512
  |line 9, col 23 to line 9, col 50 of module UserApp: 512
  line 10, col 8 to line 10, col 70 of module UserApp: 1024
`;
    const coverage = parseHandlerCoverage(SPEC, "UserApp", output);
    expect(coverage).toEqual([
      { action: "HandlePing", effectLine: 6, count: 0, inModel: true },
      { action: "HandleToggle", effectLine: 9, count: 512, inModel: true },
      { action: "HandleIdle", effectLine: 14, count: 0, inModel: false },
    ]);
    // HandleIdle is at 0 too, but no type in UserMessageTypes dispatches to it.
    expect(neverTaken(coverage ?? [])).toEqual(["HandlePing"]);
  });

  test("counts from another module do not count", () => {
    const output = `The coverage statistics at 2026-10-27 10:00:39
  line 6, col 6 to line 6, col 66 of module MessageRouter: 99
  line 9, col 6 to line 9, col 50 of module UserApp: 1
`;
    expect(neverTaken(parseHandlerCoverage(SPEC, "UserApp", output) ?? [])).toEqual(["HandlePing"]);
  });

  test("a spec without UserMessageTypes judges every handler", () => {
    const spec = SPEC.replace(/^UserMessageTypes == .*$/m, "");
    const output = "The coverage statistics at 2026-10-27 10:00:39\n";
    expect(neverTaken(parseHandlerCoverage(spec, "UserApp", output) ?? [])).toEqual([
      "HandlePing",
      "HandleToggle",
      "HandleIdle",
    ]);
  });

  test("mesh-recovery-pair: the three handlers after the pair token never run", async () => {
    const { spec, output } = await fixture("mesh-recovery-pair");
    const coverage = parseHandlerCoverage(spec, "UserApp", output);
    expect(neverTaken(coverage ?? [])).toEqual([
      "HandleOpenDataChannel",
      "HandleWriteSentinel",
      "HandleReceiveSentinel",
    ]);
  });

  test("full-featured: handlers that messages.include leaves out are not reported", async () => {
    const { spec, output } = await fixture("full-featured-excluded");
    const coverage = parseHandlerCoverage(spec, "UserApp", output) ?? [];
    expect(coverage.filter((c) => !c.inModel).map((c) => c.action)).toEqual([
      "HandleTabOpen",
      "HandleGetSettings",
      "HandleGetBookmarks",
    ]);
    expect(neverTaken(coverage)).toEqual([]);
  });
});
