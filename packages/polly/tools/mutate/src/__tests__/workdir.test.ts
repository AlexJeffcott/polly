/**
 * Scratch working directories. The engine run uses a fixture whose bunfig
 * preload is relative (Bun resolves it against the cwd, so a copied bunfig
 * would not find it) and a second target whose test reads a fixture relative
 * to `process.cwd()`, which only passes in-tree.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { existsSync, readdirSync } from "node:fs";
import { tmpdir } from "node:os";
import { runEngine } from "../engine/index.ts";
import type { EngineResult } from "../engine/types.ts";
import { absolutiseBunfig, createWorkdirs, renderToml } from "../engine/workdir.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-workdir-", {
  "bunfig.toml": '[test]\npreload = ["./tests/setup.ts"]\n',
  "tsconfig.json": JSON.stringify({ compilerOptions: { jsx: "react-jsx" } }),
  "tests/setup.ts": "Reflect.set(globalThis, '__setup', true);",
  "src/sign.ts": "export const sign = (n: number) => (n < 0 ? -1 : 1);",
  "src/greet.ts": 'export const greet = (name: string) => "hi " + name;',
  "fixtures/name.txt": "ada",
  "tests/sign.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { sign } from "../src/sign.ts";',
    "test(\"setup ran\", () => expect(Reflect.get(globalThis, '__setup')).toBe(true));",
    'test("negative", () => expect(sign(-3)).toBe(-1));',
    'test("positive", () => expect(sign(3)).toBe(1));',
  ].join("\n"),
  "tests/greet.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { readFileSync } from "node:fs";',
    'import { greet } from "../src/greet.ts";',
    'test("cwd fixture", () => expect(greet(readFileSync("fixtures/name.txt", "utf8"))).toBe("hi ada"));',
  ].join("\n"),
});

let result: EngineResult;
const logs: string[] = [];

beforeAll(async () => {
  result = await runEngine(
    {
      cwd: project.dir,
      targets: [{ file: project.path("src/sign.ts") }, { file: project.path("src/greet.ts") }],
      testInclude: ["tests/**/*.test.ts"],
      testPreload: [],
      concurrency: 2,
      timeout: { factor: 2, extraMs: 3000 },
      runner: { kind: "bun-test" },
      excludeMutators: [],
      ignoreVerifyCallsites: true,
      mode: "fast",
      coverage: "dynamic",
      cacheDir: null,
      scratchCwd: true,
      typecheck: false,
      reportPath: project.path("reports/mutation.json"),
    },
    { log: (line) => logs.push(line) }
  );
}, 120_000);
afterAll(() => project.remove());

const target = (name: string) => result.targets.find((t) => t.file.endsWith(name));

describe("scratch cwd", () => {
  test("a relative bunfig preload still loads, so the scratch baseline is green", () => {
    expect(target("sign.ts")?.inTree).toBe(false);
    expect(target("sign.ts")?.results.some((r) => r.status === "Killed")).toBe(true);
  });

  test("a target whose tests need the project cwd falls back to in-tree, and says so", () => {
    const greet = target("greet.ts");
    expect(greet?.inTree).toBe(true);
    expect(greet?.baselineMs).not.toBeNull();
    expect(greet?.results.some((r) => r.status === "Killed")).toBe(true);
    expect(logs.some((l) => l.includes("src/greet.ts") && l.includes("run in-tree"))).toBe(true);
  });

  test("no scratch directory outlives the run", () => {
    const left = readdirSync(tmpdir()).filter((d) => d.startsWith("polly-mutate-"));
    for (const d of left) expect(d.startsWith("polly-mutate-workdir-")).toBe(true);
  });
});

describe("createWorkdirs", () => {
  test("each dir carries a tsconfig that extends the project's and an absolute bunfig", async () => {
    const workdirs = createWorkdirs(project.dir);
    try {
      const dir = workdirs.create();
      expect(await Bun.file(`${dir}/tsconfig.json`).json()).toEqual({
        extends: project.path("tsconfig.json"),
      });
      const bunfig = Bun.TOML.parse(await Bun.file(`${dir}/bunfig.toml`).text());
      expect(bunfig).toEqual({ test: { preload: [project.path("tests/setup.ts")] } });
      workdirs.release(dir);
      expect(existsSync(dir)).toBe(false);
    } finally {
      workdirs.remove();
    }
    expect(existsSync(workdirs.root)).toBe(false);
  });

  test("a project with no tsconfig or bunfig gets an empty dir", () => {
    const bare = createFixtureProject("polly-mutate-bare-", { "a.txt": "1" });
    const workdirs = createWorkdirs(bare.dir);
    try {
      expect(readdirSync(workdirs.create())).toEqual([]);
    } finally {
      workdirs.remove();
      bare.remove();
    }
  });
});

describe("absolutiseBunfig", () => {
  test("resolves top-level and [test] preloads, a string or a list, and keeps the rest", () => {
    expect(
      absolutiseBunfig(
        { preload: "./tests/setup.ts", test: { preload: ["./tests/setup.ts"], timeout: 5 } },
        project.dir
      )
    ).toEqual({
      preload: project.path("tests/setup.ts"),
      test: { preload: [project.path("tests/setup.ts")], timeout: 5 },
    });
  });

  test("leaves a preload it cannot resolve as written", () => {
    expect(absolutiseBunfig({ test: { preload: "./missing.ts" } }, project.dir)).toEqual({
      test: { preload: "./missing.ts" },
    });
  });
});

describe("renderToml", () => {
  test("round-trips the shapes a bunfig holds", () => {
    const config = {
      smol: true,
      preload: ["/a b/x.ts"],
      define: { "process.env.X": '"1"' },
      test: { timeout: 5000, coverageThreshold: { line: 0.8 }, root: "src" },
      install: { scopes: { "@acme": { url: "https://x.test/" } } },
      loader: { ".txt": "text" },
      list: [{ a: 1 }],
    };
    expect(Bun.TOML.parse(renderToml(config))).toEqual(config);
  });
});
