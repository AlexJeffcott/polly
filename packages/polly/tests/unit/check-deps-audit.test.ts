import { describe, expect, test } from "bun:test";
import { parseBunAudit, parseCachedResult, parseOsvOutput } from "../../scripts/check-deps-audit";

const entry = {
  hash: "h",
  timestamp: "2026-10-23T00:00:00.000Z",
  cveCount: 0,
  cveDetails: "",
  outdated: "",
  outdatedCount: 2,
};

describe("parseCachedResult", () => {
  test("returns a well-formed entry unchanged", () => {
    expect(parseCachedResult(entry)).toEqual(entry);
  });

  test("a mistyped field is a cache miss, not a cached pass", () => {
    expect(parseCachedResult({ ...entry, cveCount: "3" })).toBeNull();
    expect(parseCachedResult({ hash: "h" })).toBeNull();
    expect(parseCachedResult([entry])).toBeNull();
  });
});

describe("parseOsvOutput", () => {
  test("keeps a vulnerability that has no id, so it still counts", () => {
    const parsed = parseOsvOutput({
      results: [{ packages: [{ package: { name: "ip" }, vulnerabilities: [{ summary: "s" }] }] }],
    });
    expect(parsed.results?.[0]?.packages?.[0]).toEqual({
      package: { name: "ip", version: undefined },
      vulnerabilities: [{ id: "<unknown>", summary: "s" }],
    });
  });

  test("a non-object is no results", () => {
    expect(parseOsvOutput(null)).toEqual({ results: [] });
  });
});

describe("parseBunAudit", () => {
  test("reads package → advisories", () => {
    expect(parseBunAudit({ qs: [{ url: "u", severity: "high", extra: 1 }] })).toEqual({
      qs: [{ url: "u", title: undefined, severity: "high", vulnerable_versions: undefined }],
    });
  });

  test("a non-array advisory list or a non-object is refused", () => {
    expect(parseBunAudit({ qs: "high" })).toBeNull();
    expect(parseBunAudit(null)).toBeNull();
  });
});
