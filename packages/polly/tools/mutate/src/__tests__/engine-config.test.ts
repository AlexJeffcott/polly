import { afterAll, describe, expect, test } from "bun:test";
import { parseMutateArgs } from "../args.ts";
import {
  engineConfigFromStryker,
  expandMutateEntries,
  preloadsFromNodeArgs,
} from "../engine-config.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-config-", {
  "src/a.ts": "export const a = 1;",
  "src/b.ts": "export const b = 2;",
  "src/b.test.ts": "",
  "stryker.conf.json": JSON.stringify({
    testRunner: "bun",
    bun: { testFiles: ["tests/**/*.test.ts"], nodeArgs: ["--preload", "./tests/setup.ts"] },
    mutate: ["src/**/*.ts", "!src/**/*.test.ts", "src/a.ts:2-4"],
    concurrency: 3,
  }),
  "command.conf.json": JSON.stringify({ testRunner: "command", mutate: ["src/a.ts"] }),
});
afterAll(() => project.remove());

const baseCfg = {
  cwd: project.dir,
  strykerConfigPath: project.path("stryker.conf.json"),
  reportPath: project.path("reports/m.json"),
  dbPath: ":memory:",
  decisionsPath: project.path("d.jsonl"),
};

describe("expandMutateEntries", () => {
  test("globs, ! exclusions and a later :from-to range on the same file", async () => {
    const targets = await expandMutateEntries(project.dir, [
      "src/**/*.ts",
      "!src/**/*.test.ts",
      "src/a.ts:2-4",
    ]);
    expect(targets).toEqual([
      { file: project.path("src/a.ts"), lines: { from: 2, to: 4 } },
      { file: project.path("src/b.ts") },
    ]);
  });
});

describe("engineConfigFromStryker", () => {
  test("reads targets, test globs and concurrency from the Stryker config", async () => {
    const cfg = await engineConfigFromStryker(baseCfg, parseMutateArgs(["run", "--engine", "bun"]));
    expect(cfg.cwd).toBe(project.dir);
    expect(cfg.testInclude).toEqual(["tests/**/*.test.ts"]);
    expect(cfg.concurrency).toBe(3);
    expect(cfg.testPreload).toEqual([project.path("tests/setup.ts")]);
    expect(cfg.targets.map((t) => t.file)).toEqual([
      project.path("src/a.ts"),
      project.path("src/b.ts"),
    ]);
  });

  test("--files and --concurrency override the config", async () => {
    const args = parseMutateArgs([
      "run",
      "--engine",
      "bun",
      "--files",
      "src/b.ts",
      "--concurrency",
      "8",
    ]);
    const cfg = await engineConfigFromStryker(baseCfg, args);
    expect(cfg.targets).toEqual([{ file: project.path("src/b.ts") }]);
    expect(cfg.concurrency).toBe(8);
  });

  test("mode, cache dir and --no-cache", async () => {
    const fast = await engineConfigFromStryker(baseCfg, parseMutateArgs([]));
    expect(fast.mode).toBe("fast");
    expect(fast.cacheDir).toBe(project.path(".polly/mutate/cache"));
    const matrix = await engineConfigFromStryker(
      baseCfg,
      parseMutateArgs(["--mode", "matrix", "--no-cache"])
    );
    expect(matrix.mode).toBe("matrix");
    expect(matrix.cacheDir).toBeNull();
  });

  test("rejects what the bun engine cannot do yet", async () => {
    await expect(
      engineConfigFromStryker(baseCfg, parseMutateArgs(["--mode", "slow"]))
    ).rejects.toThrow("expected fast or matrix");
    await expect(
      engineConfigFromStryker(baseCfg, parseMutateArgs(["--concurrency", "0"]))
    ).rejects.toThrow("positive integer");
    const commandCfg = { ...baseCfg, strykerConfigPath: project.path("command.conf.json") };
    await expect(engineConfigFromStryker(commandCfg, parseMutateArgs([]))).rejects.toThrow(
      'testRunner "command"'
    );
  });
});

describe("preloadsFromNodeArgs", () => {
  test("both flag spellings, resolved against the config dir; other args ignored", () => {
    const args = ["--smol", "--preload", "./a.ts", "--preload=b/c.ts", "--preload"];
    expect(preloadsFromNodeArgs("/p", args)).toEqual(["/p/a.ts", "/p/b/c.ts"]);
  });
});

describe("parseMutateArgs (engine flags)", () => {
  test("engine flags take values, so they are not read as the verb", () => {
    const a = parseMutateArgs(["--engine", "bun", "--since", "main", "--mode", "fast"]);
    expect(a.verb).toBe("run");
    expect(a.engine).toBe("bun");
    expect(a.since).toBe("main");
    expect(a.mode).toBe("fast");
  });
});
