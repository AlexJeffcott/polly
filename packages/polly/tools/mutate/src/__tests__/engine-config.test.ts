import { afterAll, describe, expect, test } from "bun:test";
import { join } from "node:path";
import { parseMutateArgs } from "../args.ts";
import { resolveMutateConfig } from "../config.ts";
import { parseMutationConfig } from "../define.ts";
import { engineConfigFor, expandMutateEntries } from "../engine-config.ts";
import { initConfig } from "../init.ts";
import {
  commandArgv,
  migrateConfig,
  preloadArgs,
  renderMutationConfig,
  strykerToMutation,
} from "../migrate.ts";
import { createFixtureProject } from "./fixture-project.ts";

const DEFINE = join(import.meta.dir, "../define.ts");

const project = createFixtureProject("polly-mutate-config-", {
  "src/a.ts": "export const a = 1;",
  "src/b.ts": "export const b = 2;",
  "src/b.test.ts": "",
  "polly.mutate.ts": [
    `import { defineMutation } from "${DEFINE}";`,
    "export default defineMutation({",
    '  targets: ["src/**/*.ts", "!src/**/*.test.ts", "src/a.ts:2-4"],',
    '  tests: { include: ["tests/**/*.test.ts"], preload: ["./tests/setup.ts"] },',
    "  concurrency: 3,",
    '  mutators: { exclude: ["StringLiteral"] },',
    '  report: "out/m.json",',
    "});",
  ].join("\n"),
  "stryker/stryker.conf.json": JSON.stringify({
    $schema: "x",
    testRunner: "bun",
    plugins: ["stryker-mutator-bun-runner"],
    bun: { testFiles: ["tests/**/*.test.ts"], nodeArgs: ["--preload", "./tests/setup.ts"] },
    mutate: ["src/a.ts"],
    concurrency: 2,
    timeoutMS: 9000,
    disableBail: true,
    thresholds: { high: 90, low: 70, break: 50 },
  }),
  "legacy/stryker.conf.json": JSON.stringify({
    testRunner: "bun",
    bun: { testFiles: ["tests/**/*.test.ts"] },
    mutate: ["src/**/*.ts"],
  }),
  "legacy/src/x.ts": "export const x = 1;",
  "command/stryker.conf.json": JSON.stringify({
    testRunner: "command",
    commandRunner: { command: "bun run bdd" },
    mutate: ["h.ts"],
    disableBail: true,
  }),
  "jest/stryker.conf.json": JSON.stringify({ testRunner: "jest", mutate: ["a.ts"] }),
  "bad/polly.mutate.ts": 'export default { targets: ["a.ts"], tests: { include: [] } };',
});
afterAll(() => project.remove());

const load = (dir: string, argv: string[] = []) =>
  resolveMutateConfig(project.path(dir), parseMutateArgs(argv));

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

describe("resolveMutateConfig", () => {
  test("polly.mutate.ts wins over a Stryker config in the same project", async () => {
    const cfg = await load("");
    expect(cfg.mutation?.format).toBe("polly");
    expect(cfg.mutation?.path).toBe(project.path("polly.mutate.ts"));
    // The Stryker engine still finds its own config.
    expect(cfg.strykerConfigPath).toBe(project.path("stryker/stryker.conf.json"));
    expect(cfg.reportPath).toBe(project.path("out/m.json"));
  });

  test("a Stryker config is the deprecated fallback, read through the migration mapping", async () => {
    const cfg = await load("legacy");
    expect(cfg.mutation?.format).toBe("stryker");
    expect(cfg.mutation?.config.targets).toEqual(["src/**/*.ts"]);
    expect(cfg.reportPath).toBe(project.path("legacy/reports/mutation/mutation.json"));
  });

  test("a Stryker config the mapping cannot read is not fatal; the error waits for the engine", async () => {
    const cfg = await load("jest");
    expect(cfg.mutation).toBeNull();
    expect(cfg.mutationError).toContain('testRunner "jest"');
    await expect(engineConfigFor(cfg, parseMutateArgs([]))).rejects.toThrow('testRunner "jest"');
  });

  test("an invalid polly.mutate.ts fails with the file and the field", async () => {
    await expect(load("bad")).rejects.toThrow("tests.include is empty");
  });

  test("--report on the CLI resolves against the cwd and beats the config", async () => {
    const cfg = await load("", ["--report", "r.json"]);
    expect(cfg.reportPath).toBe(project.path("r.json"));
  });
});

describe("engineConfigFor", () => {
  test("reads targets, tests, preloads, concurrency and exclusions from polly.mutate.ts", async () => {
    const cfg = await engineConfigFor(await load(""), parseMutateArgs([]));
    expect(cfg.cwd).toBe(project.dir);
    expect(cfg.runner).toEqual({ kind: "bun-test" });
    expect(cfg.testInclude).toEqual(["tests/**/*.test.ts"]);
    expect(cfg.testPreload).toEqual([project.path("tests/setup.ts")]);
    expect(cfg.concurrency).toBe(3);
    expect(cfg.excludeMutators).toEqual(["StringLiteral"]);
    expect(cfg.timeout).toEqual({ factor: 2, extraMs: 3000 });
    expect(cfg.ignoreVerifyCallsites).toBe(true);
    expect(cfg.targets).toEqual([
      { file: project.path("src/a.ts"), lines: { from: 2, to: 4 } },
      { file: project.path("src/b.ts") },
    ]);
  });

  test("--files and --concurrency override the config", async () => {
    const args = parseMutateArgs(["run", "--files", "src/b.ts", "--concurrency", "8"]);
    const cfg = await engineConfigFor(await load(""), args);
    expect(cfg.targets).toEqual([{ file: project.path("src/b.ts") }]);
    expect(cfg.concurrency).toBe(8);
  });

  test("mode, cache dir and --no-cache", async () => {
    const base = await load("");
    const fast = await engineConfigFor(base, parseMutateArgs([]));
    expect(fast.mode).toBe("fast");
    expect(fast.cacheDir).toBe(project.path(".polly/mutate/cache"));
    const matrix = await engineConfigFor(base, parseMutateArgs(["--mode", "matrix", "--no-cache"]));
    expect(matrix.mode).toBe("matrix");
    expect(matrix.cacheDir).toBeNull();
  });

  test("a command runner runs in-tree and refuses matrix mode", async () => {
    const cfg = await load("command");
    const fast = await engineConfigFor(cfg, parseMutateArgs([]));
    expect(fast.runner).toEqual({ kind: "command", argv: ["bun", "run", "bdd"] });
    expect(fast.scratchCwd).toBe(false);
    expect(fast.testInclude).toEqual([]);
    await expect(engineConfigFor(cfg, parseMutateArgs(["--mode", "matrix"]))).rejects.toThrow(
      "command runner"
    );
  });

  test("rejects bad flags", async () => {
    const base = await load("");
    await expect(engineConfigFor(base, parseMutateArgs(["--mode", "slow"]))).rejects.toThrow(
      "expected fast or matrix"
    );
    await expect(engineConfigFor(base, parseMutateArgs(["--concurrency", "0"]))).rejects.toThrow(
      "positive integer"
    );
  });
});

describe("strykerToMutation", () => {
  test("maps every key the engine has a counterpart for, and names the dropped ones", async () => {
    const raw = await Bun.file(project.path("stryker/stryker.conf.json")).json();
    const { config, notes } = strykerToMutation(raw, "s.json");
    expect(config).toEqual({
      targets: ["src/a.ts"],
      tests: { include: ["tests/**/*.test.ts"], preload: ["./tests/setup.ts"] },
      mode: "matrix",
      concurrency: 2,
      timeout: { factor: 1.5, extraMs: 9000 },
      thresholds: { break: 50 },
    });
    expect(notes.join("\n")).toContain("dropped Stryker-only keys: plugins");
    expect(notes.join("\n")).not.toContain("$schema");
  });

  test("a command runner keeps fast mode even with disableBail", () => {
    const { config } = strykerToMutation(
      { testRunner: "command", commandRunner: { command: "bun run bdd" }, disableBail: true },
      "c.json"
    );
    expect(config.runner).toEqual({ kind: "command", argv: ["bun", "run", "bdd"] });
    expect(config.mode).toBeUndefined();
  });

  test("commandArgv sends shell syntax through sh -c", () => {
    expect(commandArgv("  npm test ")).toEqual(["npm", "test"]);
    expect(commandArgv("bun test && echo ok")).toEqual(["sh", "-c", "bun test && echo ok"]);
  });

  test("preloadArgs: both flag spellings, as written; other args ignored", () => {
    const args = ["--smol", "--preload", "./a.ts", "--preload=b/c.ts", "--preload"];
    expect(preloadArgs(args)).toEqual(["./a.ts", "b/c.ts"]);
  });
});

describe("migrateConfig", () => {
  test("prints by default, writes with write, and refuses to overwrite without force", async () => {
    const stryker = project.path("legacy/stryker.conf.json");
    const dry = await migrateConfig(stryker);
    expect(dry.written).toBe(false);
    expect(await Bun.file(project.path("legacy/polly.mutate.ts")).exists()).toBe(false);

    const wrote = await migrateConfig(stryker, { write: true });
    expect(wrote.written).toBe(true);
    const migrated = await resolveMutateConfig(project.path("legacy"), parseMutateArgs([]));
    expect(migrated.mutation?.format).toBe("polly");
    expect(migrated.mutation?.config.targets).toEqual(["src/**/*.ts"]);

    expect((await migrateConfig(stryker, { write: true })).written).toBe(false);
    expect((await migrateConfig(stryker, { write: true, force: true })).written).toBe(true);
  });

  test("the rendered file is a defineMutation call that loads back to the same config", async () => {
    const config = { targets: ["a.ts"], tests: { include: ["t/**/*.test.ts"] }, concurrency: 2 };
    const source = renderMutationConfig(config, DEFINE);
    expect(source).toContain("export default defineMutation({");
    expect(source).toContain("targets: [");
    const path = project.path("render/polly.mutate.ts");
    await Bun.write(path, source);
    const back = await resolveMutateConfig(project.path("render"), parseMutateArgs([]));
    expect(back.mutation?.config).toEqual(config);
  });
});

describe("initConfig", () => {
  test("writes a polly.mutate.ts that loads", async () => {
    const dir = project.path("fresh");
    await Bun.write(join(dir, "src/x.ts"), "export const x = 1;");
    await Bun.write(join(dir, "tests/x.test.ts"), "");
    const result = await initConfig(dir);
    expect(result.created).toBe(true);
    const cfg = await resolveMutateConfig(dir, parseMutateArgs([]));
    expect(cfg.mutation?.config.tests?.include).toEqual(["tests/**/*.test.ts"]);
    expect((await initConfig(dir)).created).toBe(false);
  });
});

describe("parseMutationConfig", () => {
  test("names the field that is wrong", () => {
    expect(() => parseMutationConfig({ targets: "a.ts" }, "f")).toThrow("targets");
    expect(() => parseMutationConfig({ targets: [], mode: "slow" }, "f")).toThrow("mode");
    expect(() =>
      parseMutationConfig(
        { targets: [], tests: { include: ["t"] }, mutators: { exclude: ["Nope"] } },
        "f"
      )
    ).toThrow("unknown mutator");
    expect(() => parseMutationConfig({ targets: [], runner: { kind: "jest" } }, "f")).toThrow(
      "runner.kind"
    );
    expect(() =>
      parseMutationConfig({ targets: [], runner: { kind: "command", argv: [] } }, "f")
    ).toThrow("argv is empty");
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

  test("migrate --write --force", () => {
    const a = parseMutateArgs(["migrate", "--write", "--force"]);
    expect(a.verb).toBe("migrate");
    expect(a.write).toBe(true);
    expect(a.force).toBe(true);
  });
});
