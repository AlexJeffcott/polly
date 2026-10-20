/**
 * The engine end to end on a fixture project: real oxc parse, real import
 * graph, real `bun test` processes with the injection preload. If the preload
 * stopped applying mutants, every mutant would survive and the Killed
 * assertions below would fail — that is what makes this the injection proof.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mutationScore, runEngine } from "../engine/index.ts";
import type { EngineResult, MutantStatus } from "../engine/types.ts";
import { buildDb, type MutationReport } from "../ingest.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-engine-", {
  // clamp's upper bound is never tested, so its mutants must survive.
  "src/clamp.ts": [
    "const requires = (_c: boolean, _m: string) => {};",
    "export function clamp(x: number, lo: number, hi: number): number {",
    '  requires(lo <= hi, "lo must not exceed hi");',
    "  if (x < lo) return lo;",
    "  if (x > hi) return hi;",
    "  return x;",
    "}",
  ].join("\n"),
  "src/untested.ts": "export const flag = (a: number) => a > 1;",
  "src/broken.ts": "export const positive = (a: number) => a > 0;",
  // Stands in for a project preload such as polly's CSS-module shim: the clamp
  // tests are red without it, so a green baseline proves testPreload is passed.
  "tests/setup.ts": "Reflect.set(globalThis, '__fixtureShim', true);",
  "tests/clamp.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { clamp } from "../src/clamp.ts";',
    "test(\"preload ran\", () => expect(Reflect.get(globalThis, '__fixtureShim')).toBe(true));",
    'test("inside", () => expect(clamp(5, 0, 10)).toBe(5));',
    'test("below", () => expect(clamp(-1, 0, 10)).toBe(0));',
  ].join("\n"),
  "tests/broken.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { positive } from "../src/broken.ts";',
    'test("red before any mutation", () => expect(positive(1)).toBe(false));',
  ].join("\n"),
});

let result: EngineResult;
const reportPath = project.path("reports/mutation.json");

beforeAll(async () => {
  result = await runEngine({
    cwd: project.dir,
    targets: [
      { file: project.path("src/clamp.ts") },
      { file: project.path("src/untested.ts") },
      { file: project.path("src/broken.ts") },
    ],
    testInclude: ["tests/**/*.test.ts"],
    testPreload: [project.path("tests/setup.ts")],
    concurrency: 4,
    timeout: { factor: 2, extraMs: 3000 },
    runner: { kind: "bun-test" },
    excludeMutators: [],
    ignoreVerifyCallsites: true,
    contracts: "off",
    mode: "fast",
    coverage: "dynamic",
    cacheDir: null,
    scratchCwd: true,
    typecheck: false,
    reportPath,
  });
}, 120_000);
afterAll(() => project.remove());

function statuses(file: string): Record<string, number> {
  const t = result.targets.find((x) => x.file.endsWith(file));
  const out: Partial<Record<MutantStatus, number>> = {};
  for (const r of t?.results ?? []) out[r.status] = (out[r.status] ?? 0) + 1;
  return out;
}

describe("runEngine", () => {
  test("kills what the tests pin and leaves the untested branch alive", () => {
    const clamp = result.targets.find((t) => t.file.endsWith("clamp.ts"));
    const killedLines = new Set(
      clamp?.results.filter((r) => r.status === "Killed").map((r) => r.mutant.location.start.line)
    );
    const survivedLines = new Set(
      clamp?.results.filter((r) => r.status === "Survived").map((r) => r.mutant.location.start.line)
    );
    expect(killedLines.has(4)).toBe(true); // if (x < lo) return lo;
    expect(survivedLines.has(5)).toBe(true); // if (x > hi) return hi;
    expect(clamp?.coveringTests).toEqual([project.path("tests/clamp.test.ts")]);
  });

  test("mutants inside requires() are reported Ignored and never run", () => {
    const clamp = result.targets.find((t) => t.file.endsWith("clamp.ts"));
    const ignored = clamp?.results.filter((r) => r.status === "Ignored") ?? [];
    expect(ignored.length).toBeGreaterThan(0);
    expect(
      ignored.every((r) => r.mutant.location.start.line === 3 && r.durationMs === undefined)
    ).toBe(true);
  });

  test("a target no test imports is NoCoverage", () => {
    expect(Object.keys(statuses("untested.ts"))).toEqual(["NoCoverage"]);
  });

  test("a target whose selected tests are red before mutation is RuntimeError, not Killed", () => {
    expect(Object.keys(statuses("broken.ts"))).toEqual(["RuntimeError"]);
    const reason = result.targets.find((t) => t.file.endsWith("broken.ts"))?.results[0]
      ?.statusReason;
    expect(reason).toContain("baseline red");
  });

  test("score counts NoCoverage as undetected and leaves Ignored out", () => {
    const clamp = result.targets.find((t) => t.file.endsWith("clamp.ts"));
    const score = mutationScore(clamp?.results ?? []);
    expect(score).toBeGreaterThan(0);
    expect(score).toBeLessThan(100);
    const untested = result.targets.find((t) => t.file.endsWith("untested.ts"));
    expect(mutationScore(untested?.results ?? [])).toBe(0);
  });

  test("the written report loads into the kill-matrix db the analysis reads", async () => {
    const report: MutationReport = await Bun.file(reportPath).json();
    expect(Object.keys(report.files).sort()).toEqual([
      "src/broken.ts",
      "src/clamp.ts",
      "src/untested.ts",
    ]);
    const db = buildDb(report);
    try {
      const row = db.query("SELECT COUNT(*) AS n FROM mutants").get();
      const total = result.targets.reduce((n, t) => n + t.results.length, 0);
      expect(row).toEqual({ n: total });
    } finally {
      db.close();
    }
  });
});
