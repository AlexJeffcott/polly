import { describe, expect, test } from "bun:test";
import { type CheckRunResult, digestRun, summariseRunReport } from "@fairfox/polly/quality";

function r(id: string, ok: boolean, messages: string[] = []): CheckRunResult {
  return { id, ok, durationMs: 1, cached: false, messages };
}

describe("digestRun", () => {
  test("identical inputs in different orders hash to the same value", () => {
    const sha = "0000000000000000000000000000000000000000";
    const a = digestRun(sha, [r("polly:a", true), r("polly:b", true)]);
    const b = digestRun(sha, [r("polly:b", true), r("polly:a", true)]);
    expect(a).toBe(b);
  });

  test("changing one result changes the digest", () => {
    const sha = "0000000000000000000000000000000000000000";
    const a = digestRun(sha, [r("polly:a", true)]);
    const b = digestRun(sha, [r("polly:a", false, ["broken"])]);
    expect(a).not.toBe(b);
  });

  test("durationMs and cached do not contribute to the digest", () => {
    const sha = "0000000000000000000000000000000000000000";
    const fresh: CheckRunResult = {
      id: "polly:a",
      ok: true,
      durationMs: 5,
      cached: false,
      messages: [],
    };
    const cached: CheckRunResult = {
      id: "polly:a",
      ok: true,
      durationMs: 50,
      cached: true,
      messages: [],
    };
    expect(digestRun(sha, [fresh])).toBe(digestRun(sha, [cached]));
  });

  test("changing the commit sha changes the digest", () => {
    const a = digestRun("a".repeat(40), [r("polly:a", true)]);
    const b = digestRun("b".repeat(40), [r("polly:a", true)]);
    expect(a).not.toBe(b);
  });
});

describe("summariseRunReport", () => {
  test("counts passing checks", () => {
    const summary = summariseRunReport({
      ok: false,
      results: [r("a", true), r("b", false), r("c", true)],
      totalDurationMs: 0,
    });
    expect(summary).toBe("2/3 checks passed");
  });

  test("handles empty result list", () => {
    const summary = summariseRunReport({ ok: true, results: [], totalDurationMs: 0 });
    expect(summary).toBe("0/0 checks passed");
  });
});
