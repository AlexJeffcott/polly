/**
 * The two files `polly mutate` reads back from disk — the mutation report and
 * the decisions log — are checked against the shape their readers use, so a
 * malformed file fails where it is read, naming it, rather than as an
 * undefined field deep in the SQL ingest or the staleness join.
 */
import { afterAll, describe, expect, test } from "bun:test";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { loadDecisions } from "../decisions.ts";
import { isMutationReport, loadMutationReport } from "../ingest.ts";

const dir = mkdtempSync(join(tmpdir(), "polly-mutate-load-"));
afterAll(() => rmSync(dir, { recursive: true, force: true }));

const mutant = {
  id: "1",
  mutatorName: "ArithmeticOperator",
  status: "Killed",
  location: { start: { line: 1, column: 1 }, end: { line: 1, column: 5 } },
  replacement: "n / 2",
  killedBy: ["t1"],
};
const report = {
  schemaVersion: "1",
  thresholds: { high: 80, low: 60 },
  files: { "src/a.ts": { language: "typescript", source: "", mutants: [mutant] } },
  testFiles: { "tests/a.test.ts": { tests: [{ id: "t1", name: "a" }] } },
  contracts: {
    mode: "ensures",
    runner: "bun-test",
    sites: [{ id: "src/a.ts:3", file: "src/a.ts", line: 3, primitive: "ensures" }],
    violations: [],
  },
};

describe("isMutationReport", () => {
  test("accepts a schema report and keeps fields outside the read shape", () => {
    expect(isMutationReport(report)).toBe(true);
  });

  test("refuses a mutant whose killers are not strings", () => {
    const bad = { ...report, files: { "src/a.ts": { mutants: [{ ...mutant, killedBy: [1] }] } } };
    expect(isMutationReport(bad)).toBe(false);
  });

  test("refuses an unknown contracts mode and a missing files map", () => {
    expect(isMutationReport({ ...report, contracts: { ...report.contracts, mode: "x" } })).toBe(
      false
    );
    expect(isMutationReport({ schemaVersion: "1" })).toBe(false);
  });
});

describe("loadMutationReport", () => {
  test("returns the parsed report", async () => {
    const path = join(dir, "ok.json");
    writeFileSync(path, JSON.stringify(report));
    expect<unknown>(await loadMutationReport(path)).toEqual(report);
  });

  test("throws naming the file when it is not a report", async () => {
    const path = join(dir, "bad.json");
    writeFileSync(path, JSON.stringify({ files: [] }));
    await expect(loadMutationReport(path)).rejects.toThrow(`${path} is not a mutation report`);
  });
});

describe("loadDecisions", () => {
  const decision = {
    file: "tests/a.test.ts",
    verdict: "keep",
    rationale: "",
    signal: { kills: 2, uniqueKills: 0, subsumed: true },
    hash: null,
    decided: "2026-10-23",
  };

  test("last write wins per file", async () => {
    const path = join(dir, "ok.jsonl");
    const later = { ...decision, verdict: "prune" };
    writeFileSync(path, `${JSON.stringify(decision)}\n\n${JSON.stringify(later)}\n`);
    const loaded = await loadDecisions(path);
    expect(loaded.get("tests/a.test.ts")).toEqual(later);
  });

  test("a line that is not a decision throws, naming the line", async () => {
    const path = join(dir, "bad.jsonl");
    writeFileSync(path, `${JSON.stringify(decision)}\n${JSON.stringify({ file: "x" })}\n`);
    await expect(loadDecisions(path)).rejects.toThrow(`${path}:2 is not a decision record`);
  });
});
