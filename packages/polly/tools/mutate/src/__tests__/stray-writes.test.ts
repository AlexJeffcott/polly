/**
 * The stray-write guard on a real git repo and a real engine run. `outDir`'s
 * fallback branch is a relative path, so a mutant that forces it writes into
 * the fixture repo — the shape of polly's storage-adapter `st/orage-adapter-id`
 * leak. The baseline test also writes a file of its own, which must be
 * attributed to the baseline and not to the mutants.
 *
 * The guard run uses `scratchCwd: false`, so the leak reaches the repo; the
 * scratch run shows the same mutants leave the repo untouched.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { existsSync, mkdirSync, writeFileSync } from "node:fs";
import { runEngine } from "../engine/index.ts";
import { newPaths, snapshotWorktree } from "../engine/stray-writes.ts";
import type { EngineResult } from "../engine/types.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-stray-", {
  ".gitignore": "*.log\n",
  "src/out.ts": 'export const outDir = (tmp: string) => (tmp.length > 0 ? tmp : "stray");',
  "tests/out.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";',
    'import { tmpdir } from "node:os";',
    'import { join } from "node:path";',
    'import { outDir } from "../src/out.ts";',
    'test("writes under the temp dir", () => {',
    '  const tmp = mkdtempSync(join(tmpdir(), "polly-stray-"));',
    "  const dir = outDir(tmp);",
    "  mkdirSync(dir, { recursive: true });",
    '  writeFileSync(join(dir, "x.txt"), "1");',
    '  writeFileSync("baseline-side-effect.txt", "1");',
    "  expect(dir).toBe(tmp);",
    "});",
  ].join("\n"),
});
Bun.spawnSync(["git", "init", "-q"], { cwd: project.dir });

const run = (scratchCwd: boolean) =>
  runEngine({
    cwd: project.dir,
    targets: [{ file: project.path("src/out.ts") }],
    testInclude: ["tests/**/*.test.ts"],
    testPreload: [],
    concurrency: 2,
    timeout: { factor: 2, extraMs: 3000 },
    ignoreVerifyCallsites: true,
    mode: "fast",
    cacheDir: null,
    scratchCwd,
    reportPath: project.path("reports/mutation.json"),
  });

let result: EngineResult;
let scratch: EngineResult;

beforeAll(async () => {
  scratch = await run(true);
  result = await run(false);
}, 120_000);
afterAll(() => project.remove());

describe("stray-write guard", () => {
  test("a write by a mutant run is reported and left on disk", () => {
    expect(result.strayWrites?.mutants).toEqual(["stray/x.txt"]);
    expect(existsSync(project.path("stray/x.txt"))).toBe(true);
  });

  test("a write by the unmutated tests is attributed to the baseline", () => {
    expect(result.strayWrites?.baseline).toEqual(["baseline-side-effect.txt"]);
  });

  test("the report the engine writes on purpose is not a stray write", () => {
    expect(existsSync(project.path("reports/mutation.json"))).toBe(true);
    expect(JSON.stringify(result.strayWrites)).not.toContain("reports/");
  });

  test("with a scratch cwd the same mutants and tests write nothing into the repo", () => {
    expect(scratch.strayWrites).toEqual({ root: project.dir, baseline: [], mutants: [] });
    expect(scratch.targets[0]?.inTree).toBe(false);
    expect(scratch.targets[0]?.results.some((r) => r.status === "Killed")).toBe(true);
  });

  test("snapshots see new files in untracked dirs, ignored files and modified ones", () => {
    const before = snapshotWorktree(project.dir);
    writeFileSync(project.path("stray/y.txt"), "1");
    writeFileSync(project.path("debug.log"), "1");
    mkdirSync(project.path("deep/er"), { recursive: true });
    writeFileSync(project.path("deep/er/z.txt"), "1");
    expect(newPaths(before, snapshotWorktree(project.dir))).toEqual([
      "debug.log",
      "deep/er/z.txt",
      "stray/y.txt",
    ]);
  });

  test("outside a git worktree there is no snapshot and no report", () => {
    const bare = createFixtureProject("polly-mutate-nogit-", { "a.txt": "1" });
    try {
      expect(snapshotWorktree(bare.dir)).toBeNull();
      expect(newPaths(null, null)).toEqual([]);
    } finally {
      bare.remove();
    }
  });
});
