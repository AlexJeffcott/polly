/**
 * The result cache on a real engine run. A second run with nothing changed
 * must reuse every result; a change to the target, to a covering test, or to
 * a file the target imports must rerun that target, and only that target.
 */
import { afterAll, describe, expect, test } from "bun:test";
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { runEngine } from "../engine/index.ts";
import type { EngineConfig, EngineResult } from "../engine/types.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-cache-", {
  "src/base.ts": "export const base = 10;",
  "src/add.ts": 'import { base } from "./base.ts";\nexport const add = (n: number) => n + base;',
  "src/neg.ts": "export const neg = (n: number) => -n;",
  "tests/add.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { add } from "../src/add.ts";',
    'test("add", () => expect(add(1)).toBe(11));',
  ].join("\n"),
  "tests/neg.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { neg } from "../src/neg.ts";',
    'test("neg", () => expect(neg(2)).toBe(-2));',
  ].join("\n"),
});
afterAll(() => project.remove());

const cacheDir = project.path(".polly/mutate/cache");
const config = (over: Partial<EngineConfig> = {}): EngineConfig => ({
  cwd: project.dir,
  targets: [{ file: project.path("src/add.ts") }, { file: project.path("src/neg.ts") }],
  testInclude: ["tests/**/*.test.ts"],
  testPreload: [],
  mode: "matrix",
  coverage: "dynamic",
  concurrency: 4,
  timeout: { factor: 2, extraMs: 3000 },
  runner: { kind: "bun-test" },
  excludeMutators: [],
  ignoreVerifyCallsites: true,
  contracts: "off",
  scratchCwd: true,
  typecheck: false,
  cacheDir,
  reportPath: project.path("reports/mutation.json"),
  ...over,
});
const cachedFlags = (r: EngineResult) => r.targets.map((t) => t.cached);
const view = (r: EngineResult) =>
  r.targets.map((t) => t.results.map((x) => [x.mutant.mutatorName, x.status, x.killedBy]));
const append = (rel: string, text: string) =>
  writeFileSync(project.path(rel), readFileSync(project.path(rel), "utf8") + text);

describe("result cache", () => {
  let first: EngineResult;

  test("a first run fills the cache, and the cache dir ignores itself", async () => {
    first = await runEngine(config());
    expect(cachedFlags(first)).toEqual([false, false]);
    const entries = readdirSync(cacheDir).filter((f) => f.endsWith(".json"));
    expect(entries.filter((f) => f.startsWith("coverage-")).length).toBe(1);
    expect(entries.length).toBe(3);
    expect(readFileSync(`${cacheDir}/.gitignore`, "utf8")).toBe("*\n");
  }, 120_000);

  test("an unchanged second run reuses every result, killers included", async () => {
    const second = await runEngine(config());
    expect(cachedFlags(second)).toEqual([true, true]);
    expect(view(second)).toEqual(view(first));
    expect(second.targets[0]?.tests).toEqual(first.targets[0]?.tests);
  }, 120_000);

  test("a change to a file the target imports reruns that target only", async () => {
    append("src/base.ts", "\n// touched");
    expect(cachedFlags(await runEngine(config()))).toEqual([false, true]);
  }, 120_000);

  test("a change to a covering test reruns that target only", async () => {
    append("tests/neg.test.ts", "\n// touched");
    expect(cachedFlags(await runEngine(config()))).toEqual([true, false]);
  }, 120_000);

  test("a change to the target reruns it", async () => {
    append("src/add.ts", "\nexport const sub = (n: number) => n - base;");
    expect(cachedFlags(await runEngine(config()))).toEqual([false, true]);
  }, 120_000);

  test("another contracts mode is another key", async () => {
    expect(cachedFlags(await runEngine(config({ contracts: "all" })))).toEqual([false, false]);
  }, 120_000);

  test("another mode is another key; no cache dir runs everything", async () => {
    expect(cachedFlags(await runEngine(config({ mode: "fast" })))).toEqual([false, false]);
    expect(cachedFlags(await runEngine(config({ cacheDir: null })))).toEqual([false, false]);
  }, 120_000);
});

// fairfox: polly.mutate.ts in packages/server, bun.lock at the root. The key
// hashed the absent packages/server/bun.lock, so installing typescript-7 (or
// any dependency change) reused results computed before it.
describe("result cache in a workspace", () => {
  const workspace = createFixtureProject("polly-mutate-cache-ws-", {
    "bun.lock": '{ "lockfileVersion": 1 }\n',
    "packages/app/src/neg.ts": "export const neg = (n: number) => -n;",
    "packages/app/tests/neg.test.ts": [
      'import { expect, test } from "bun:test";',
      'import { neg } from "../src/neg.ts";',
      'test("neg", () => expect(neg(2)).toBe(-2));',
    ].join("\n"),
  });
  afterAll(() => workspace.remove());
  const app = (rel: string) => workspace.path(`packages/app/${rel}`);
  const wsConfig = (): EngineConfig =>
    config({
      cwd: app(""),
      targets: [{ file: app("src/neg.ts") }],
      cacheDir: app(".polly/mutate/cache"),
      reportPath: app("reports/mutation.json"),
    });

  test("a change to the root bun.lock reruns the target", async () => {
    expect(cachedFlags(await runEngine(wsConfig()))).toEqual([false]);
    expect(cachedFlags(await runEngine(wsConfig()))).toEqual([true]);
    writeFileSync(workspace.path("bun.lock"), '{ "lockfileVersion": 1, "packages": {} }\n');
    expect(cachedFlags(await runEngine(wsConfig()))).toEqual([false]);
  }, 120_000);
});
