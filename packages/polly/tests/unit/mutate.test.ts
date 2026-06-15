import { describe, expect, test } from "bun:test";
import { parseMutateArgs } from "../../tools/mutate/src/args.ts";
import { buildDb, type MutationReport } from "../../tools/mutate/src/ingest.ts";
import { report } from "../../tools/mutate/src/report.ts";
import { isMatrixComplete } from "../../tools/mutate/src/verify-matrix.ts";

// Minimal report: t1 & t2 both kill m1 (redundant), t1 alone kills m2 (unique),
// m3 Survived (theatre), m4 NoCoverage (gap). A complete matrix because m1 has
// >1 killer and not every mutant is NoCoverage.
function sampleReport(): MutationReport {
  return {
    schemaVersion: "1",
    files: {
      "src/a.ts": {
        mutants: [
          {
            id: "m1",
            mutatorName: "X",
            status: "Killed",
            location: { start: { line: 1, column: 1 } },
            killedBy: ["t1", "t2"],
          },
          {
            id: "m2",
            mutatorName: "X",
            status: "Killed",
            location: { start: { line: 2, column: 1 } },
            killedBy: ["t1"],
          },
          {
            id: "m3",
            mutatorName: "X",
            status: "Survived",
            location: { start: { line: 3, column: 1 } },
          },
          {
            id: "m4",
            mutatorName: "X",
            status: "NoCoverage",
            location: { start: { line: 4, column: 1 } },
          },
        ],
      },
    },
    testFiles: {
      "tests/a.test.ts": {
        tests: [
          { id: "t1", name: "t1", location: { start: { line: 1, column: 1 } } },
          { id: "t2", name: "t2", location: { start: { line: 2, column: 1 } } },
        ],
      },
    },
  };
}

describe("isMatrixComplete — the redundancy-analysis gate", () => {
  test("true when a mutant has >1 killer and coverage exists", () => {
    expect(isMatrixComplete(sampleReport())).toBe(true);
  });

  test("false when every killedBy collapses to ≤1 (bail / unpatched runner)", () => {
    const r = sampleReport();
    for (const f of Object.values(r.files))
      for (const m of f.mutants) if (m.killedBy) m.killedBy = m.killedBy.slice(0, 1);
    expect(isMatrixComplete(r)).toBe(false);
  });

  test("false when the coverage dump broke (all NoCoverage)", () => {
    const r = sampleReport();
    for (const f of Object.values(r.files)) for (const m of f.mutants) m.status = "NoCoverage";
    expect(isMatrixComplete(r)).toBe(false);
  });
});

describe("report — section gating on matrix completeness", () => {
  test("complete matrix surfaces redundancy + subsumption", () => {
    const db = buildDb(sampleReport());
    const out = report(db);
    db.close();
    expect(out).toContain("REDUNDANCY RATIO");
    expect(out).toContain("SUBSUMED");
    expect(out).toContain("THEATRE");
  });

  test("degraded matrix suppresses redundancy, keeps score/gaps/theatre + warning", () => {
    const db = buildDb(sampleReport());
    const out = report(db, { matrixComplete: false });
    db.close();
    expect(out).not.toContain("REDUNDANCY RATIO");
    expect(out).not.toContain("SUBSUMED");
    expect(out).toContain("KILL MATRIX INCOMPLETE");
    expect(out).toContain("MUTATION  score");
    expect(out).toContain("THEATRE");
  });
});

describe("parseMutateArgs", () => {
  test("bare invocation defaults to the run verb", () => {
    expect(parseMutateArgs([]).verb).toBe("run");
  });

  test("parses a verb and a value flag", () => {
    const a = parseMutateArgs(["report", "--report", "x.json"]);
    expect(a.verb).toBe("report");
    expect(a.report).toBe("x.json");
  });

  test("decisions decide keeps the trailing positionals", () => {
    const a = parseMutateArgs(["decisions", "decide", "f.ts", "keep", "why"]);
    expect(a.verb).toBe("decisions");
    expect(a.rest).toEqual(["decide", "f.ts", "keep", "why"]);
  });

  test("an unknown verb is preserved so the CLI can reject it", () => {
    expect(parseMutateArgs(["bogus"]).verb).toBe("bogus");
  });

  test("--no-report and -h are recognised", () => {
    const a = parseMutateArgs(["run", "--no-report", "-h"]);
    expect(a.noReport).toBe(true);
    expect(a.help).toBe(true);
  });

  test("init verb and --force flag", () => {
    const a = parseMutateArgs(["init", "--force"]);
    expect(a.verb).toBe("init");
    expect(a.force).toBe(true);
  });
});
