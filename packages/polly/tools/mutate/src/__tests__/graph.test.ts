import { afterAll, describe, expect, test } from "bun:test";
import { buildImportGraph, coveringTests, findTestFiles } from "../engine/graph.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-graph-", {
  "tsconfig.json": JSON.stringify({
    compilerOptions: { baseUrl: ".", paths: { "@/*": ["./src/*"] } },
  }),
  "src/leaf.ts": "export const leaf = 1;",
  "src/mid.ts": 'import { leaf } from "./leaf";\nexport const mid = leaf + 1;',
  "src/index.ts": 'export { mid } from "./mid";',
  "src/orphan.ts": "export const orphan = 0;",
  "tests/via-alias-barrel.test.ts":
    'import { mid } from "@/index";\nimport { test } from "bun:test";\ntest("t", () => void mid);',
  "tests/direct.test.ts":
    'import { leaf } from "../src/leaf.ts";\nimport { test } from "bun:test";\ntest("t", () => void leaf);',
  "tests/unrelated.test.ts": 'import { test } from "bun:test";\ntest("t", () => {});',
  "node_modules/dep/index.js": 'import "../../src/orphan.ts";',
});
afterAll(() => project.remove());

describe("static test selection", () => {
  test("follows the tsconfig alias and a re-exporting barrel to the leaf", async () => {
    const tests = await findTestFiles(project.dir, ["tests/**/*.test.ts"]);
    const graph = await buildImportGraph(tests);
    expect(coveringTests(graph, project.path("src/leaf.ts"))).toEqual([
      project.path("tests/direct.test.ts"),
      project.path("tests/via-alias-barrel.test.ts"),
    ]);
    expect(coveringTests(graph, project.path("src/mid.ts"))).toEqual([
      project.path("tests/via-alias-barrel.test.ts"),
    ]);
  });

  test("a file no test imports has no covering tests", async () => {
    const graph = await buildImportGraph(await findTestFiles(project.dir, ["tests/**/*.test.ts"]));
    expect(coveringTests(graph, project.path("src/orphan.ts"))).toEqual([]);
  });

  test("test discovery skips node_modules", async () => {
    const found = await findTestFiles(project.dir, ["**/*.js", "tests/*.test.ts"]);
    expect(found.some((f) => f.includes("/node_modules/"))).toBe(false);
    expect(found.length).toBe(3);
  });

  test("a ! entry excludes files the other entries match", async () => {
    const found = await findTestFiles(project.dir, ["tests/*.test.ts", "!tests/unrelated.test.ts"]);
    expect(found).toEqual([
      project.path("tests/direct.test.ts"),
      project.path("tests/via-alias-barrel.test.ts"),
    ]);
  });
});
