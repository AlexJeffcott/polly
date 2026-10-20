import { describe, expect, test } from "bun:test";
import {
  contractKills,
  contractsIn,
  killers,
  loadFailureId,
  parseJunit,
  testId,
} from "../engine/junit.ts";

// Shaped like Bun 1.4.3's output: one suite per file, one per describe.
const XML = `<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="bun test" tests="4">
  <testsuite name="tests/a.test.ts" file="tests/a.test.ts" tests="4">
    <testsuite name="outer" file="tests/a.test.ts" line="2" tests="3">
      <testsuite name="inner &lt;&amp;&gt;" file="tests/a.test.ts" line="3" tests="2">
        <testcase name="passes" classname="inner &lt;&amp;&gt; &gt; outer" file="tests/a.test.ts" line="4" />
        <testcase name="fails &quot;q&quot;" classname="inner &lt;&amp;&gt; &gt; outer" file="tests/a.test.ts" line="5">
          <failure type="AssertionError" message="Expected: 2&#10;Received: 1">x</failure>
        </testcase>
      </testsuite>
      <testcase name="skipped" classname="outer" file="tests/a.test.ts" line="7">
        <skipped />
      </testcase>
    </testsuite>
    <testcase name="top" classname="" file="/abs/tests/b.test.ts" line="9" />
  </testsuite>
</testsuites>`;

describe("parseJunit", () => {
  const cases = parseJunit(XML, "/proj");

  test("full names come from the describe nesting, outermost first, entities decoded", () => {
    expect(cases.map((c) => c.name)).toEqual([
      "outer > inner <&> > passes",
      'outer > inner <&> > fails "q"',
      "outer > skipped",
      "top",
    ]);
  });

  test("status, line, and file resolved against the run's cwd", () => {
    expect(cases.map((c) => [c.status, c.line, c.file])).toEqual([
      ["passed", 4, "/proj/tests/a.test.ts"],
      ["failed", 5, "/proj/tests/a.test.ts"],
      ["skipped", 7, "/proj/tests/a.test.ts"],
      ["passed", 9, "/abs/tests/b.test.ts"],
    ]);
  });

  test("no report means no cases", () => {
    expect(parseJunit("", "/proj")).toEqual([]);
  });
});

describe("killers", () => {
  const a = "/proj/tests/a.test.ts";
  const b = "/proj/tests/b.test.ts";

  test("every failed case, by the same id the test list uses", () => {
    const ids = killers(parseJunit(XML, "/proj"), new Set([a]), "/proj");
    expect(ids).toEqual([testId("/proj", a, 'outer > inner <&> > fails "q"', 5)]);
    expect(ids[0]).toBe('tests/a.test.ts#outer > inner <&> > fails "q"@5');
  });

  test("a file the baseline reported and the mutant run did not is a killer stand-in", () => {
    const onlyA = parseJunit(XML, "/proj").filter((c) => c.file === a);
    const ids = killers(onlyA, new Set([a, b]), "/proj");
    expect(ids).toContain(loadFailureId("/proj", b));
    expect(loadFailureId("/proj", b)).toBe("tests/b.test.ts#(file produced no results)@0");
  });

  test("a file with no tests, absent from the baseline too, is not", () => {
    expect(killers([], new Set(), "/proj")).toEqual([]);
  });
});

describe("contract markers", () => {
  // Shaped like Bun 1.4.3's output for an afterEach-raised error and a direct throw.
  const xml = `<testsuites name="bun test">
  <testsuite name="tests/c.test.ts" file="tests/c.test.ts">
    <testcase name="ensures" file="tests/c.test.ts" line="3">
      <failure type="Error" message="[polly-contract ensures /proj/src/h.ts:50] must &quot;hold&quot; &amp; more">Error: [polly-contract ensures /proj/src/h.ts:50] must &quot;hold&quot; &amp; more&#10;      at pre.ts:3:137&#10;</failure>
    </testcase>
    <testcase name="assertion" file="tests/c.test.ts" line="4">
      <failure type="AssertionError" message="Expected: 2&#10;Received: 1">x</failure>
    </testcase>
    <testcase name="two" file="tests/c.test.ts" line="5">
      <failure message="[polly-contract requires /proj/src/h.ts:12] a&#10;[polly-contract ensures /proj/src/h.ts:50] b&#10;[polly-contract ensures /proj/src/h.ts:50] b again">y</failure>
    </testcase>
    <testcase name="green" file="tests/c.test.ts" line="6" />
  </testsuite>
</testsuites>`;
  const cases = parseJunit(xml, "/proj");

  test("a failed case carries its decoded failure text; a passed one does not", () => {
    expect(cases[0]?.failureMessage).toBe(
      '[polly-contract ensures /proj/src/h.ts:50] must "hold" & more\nError: [polly-contract ensures /proj/src/h.ts:50] must "hold" & more\n      at pre.ts:3:137\n'
    );
    expect(cases[1]?.failureMessage).toBe("Expected: 2\nReceived: 1\nx");
    expect(cases[3]?.failureMessage).toBeUndefined();
  });

  test("contractsIn: every marker, relative to the project, sorted and unique", () => {
    expect(contractsIn(cases[2]?.failureMessage ?? "", "/proj")).toEqual([
      "src/h.ts:12",
      "src/h.ts:50",
    ]);
    expect(contractsIn("Expected: 2", "/proj")).toEqual([]);
  });

  test("contractKills: the failed cases that name a contract, by test id", () => {
    expect(contractKills(cases, "/proj")).toEqual([
      { test: "tests/c.test.ts#ensures@3", contracts: ["src/h.ts:50"] },
      { test: "tests/c.test.ts#two@5", contracts: ["src/h.ts:12", "src/h.ts:50"] },
    ]);
  });
});
