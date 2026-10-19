import { describe, expect, test } from "bun:test";
import { killers, loadFailureId, parseJunit, testId } from "../engine/junit.ts";

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
