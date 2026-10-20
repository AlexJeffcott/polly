/**
 * The command runner end to end: a `package.json` script that starts a
 * second Bun process, as `bun run bdd` → `polly bdd run` does. The mutant
 * reaches that grandchild only through BUN_OPTIONS, so a Killed result on
 * the checked branch is the proof that the injection crosses process
 * boundaries; the unchecked branch must survive.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { existsSync } from "node:fs";
import { runEngine } from "../engine/index.ts";
import { runBunTest } from "../engine/runner.ts";
import type { EngineResult } from "../engine/types.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-command-", {
  "package.json": JSON.stringify({ private: true, scripts: { check: "bun check.ts" } }),
  "src/sign.ts": [
    "export function sign(x: number): string {",
    '  if (x > 0) return "pos";',
    '  return x < 0 ? "neg" : "zero";',
    "}",
  ].join("\n"),
  // Checks the positive branch only.
  "check.ts": [
    'import { sign } from "./src/sign.ts";',
    'if (sign(2) !== "pos") process.exit(1);',
  ].join("\n"),
});

let result: EngineResult;

beforeAll(async () => {
  result = await runEngine({
    cwd: project.dir,
    targets: [{ file: project.path("src/sign.ts") }],
    runner: { kind: "command", argv: ["bun", "run", "check"] },
    testInclude: [],
    testPreload: [],
    concurrency: 4,
    timeout: { factor: 2, extraMs: 3000 },
    excludeMutators: [],
    ignoreVerifyCallsites: true,
    contracts: "off",
    mode: "fast",
    coverage: "dynamic",
    cacheDir: project.path(".polly/mutate/cache"),
    scratchCwd: false,
    typecheck: false,
    reportPath: project.path("reports/mutation.json"),
  });
}, 120_000);
afterAll(() => project.remove());

function linesWith(status: string): Set<number> {
  const results = result.targets[0]?.results ?? [];
  return new Set(
    results.filter((r) => r.status === status).map((r) => r.mutant.location.start.line)
  );
}

describe("command runner", () => {
  test("kills on the checked branch through a nested bun process; the rest survives", () => {
    expect(linesWith("Killed").has(2)).toBe(true);
    expect(linesWith("Survived").has(3)).toBe(true);
    expect(linesWith("NoCoverage").size).toBe(0);
  });

  test("never caches: nothing bounds what a command reads", () => {
    expect(result.targets[0]?.cached).toBe(false);
    expect(existsSync(project.path(".polly/mutate/cache"))).toBe(false);
  });

  test("matrix mode is refused", async () => {
    await expect(
      runEngine({
        cwd: project.dir,
        targets: [],
        runner: { kind: "command", argv: ["true"] },
        testInclude: [],
        testPreload: [],
        concurrency: 1,
        timeout: { factor: 2, extraMs: 3000 },
        excludeMutators: [],
        ignoreVerifyCallsites: true,
        contracts: "off",
        mode: "matrix",
        coverage: "dynamic",
        cacheDir: null,
        scratchCwd: false,
        typecheck: false,
        reportPath: project.path("reports/m.json"),
      })
    ).rejects.toThrow("command runner");
  });

  test("a timeout kills the command's whole process tree", async () => {
    const marker = "37.4242";
    const outcome = await runBunTest(
      { cwd: project.dir, files: [], preloads: [], bail: false, timeoutMs: 300 },
      { kind: "command", argv: ["sh", "-c", `sleep ${marker} & sleep ${marker}; true`] }
    );
    expect(outcome.timedOut).toBe(true);
    await Bun.sleep(200);
    const left = Bun.spawnSync(["pgrep", "-f", `sleep ${marker}`])
      .stdout.toString()
      .trim();
    expect(left).toBe("");
  });
});
