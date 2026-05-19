import { describe, expect, test } from "bun:test";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  type Check,
  listChecks,
  type QualityPlugin,
  registerPlugins,
  runChecks,
  validateRunConfig,
} from "@fairfox/polly/quality";

function trivialCheck(id: string, ok = true, messages: string[] = []): Check<unknown> {
  return {
    id,
    description: `trivial ${id}`,
    run: async () => ({ ok, messages }),
  };
}

function plugin(name: string, checks: Check<unknown>[]): QualityPlugin {
  return { name, version: "0.0.0", checks };
}

describe("registerPlugins", () => {
  test("registers all checks under namespaced ids", () => {
    const reg = registerPlugins([
      plugin("polly", [trivialCheck("polly:a"), trivialCheck("polly:b")]),
      plugin("ext", [trivialCheck("ext:x")]),
    ]);
    expect(reg.size).toBe(3);
    expect(reg.has("polly:a")).toBe(true);
    expect(reg.has("ext:x")).toBe(true);
  });

  test("rejects duplicate plugin name", () => {
    expect(() =>
      registerPlugins([plugin("polly", [trivialCheck("polly:a")]), plugin("polly", [])])
    ).toThrow(/plugin name collision/);
  });

  test("rejects duplicate check id within a plugin", () => {
    expect(() =>
      registerPlugins([plugin("p", [trivialCheck("p:x"), trivialCheck("p:x")])])
    ).toThrow(/Check id collision/);
  });

  test("rejects check whose id does not begin with its plugin namespace", () => {
    expect(() => registerPlugins([plugin("polly", [trivialCheck("wrong:x")])])).toThrow(
      /id does not begin/
    );
  });
});

describe("validateRunConfig", () => {
  const reg = registerPlugins([
    plugin("polly", [
      {
        id: "polly:a",
        description: "with validate",
        validate: (cfg) => {
          if (typeof cfg !== "object" || cfg === null) return ["expected object"];
          return null;
        },
        run: async () => ({ ok: true, messages: [] }),
      },
    ]),
  ]);

  test("returns no errors for valid input", () => {
    const errs = validateRunConfig(reg, {
      plugins: [],
      checks: { "polly:a": { foo: 1 } },
    });
    expect(errs).toEqual([]);
  });

  test("returns errors for invalid input, prefixed with the check id", () => {
    const errs = validateRunConfig(reg, {
      plugins: [],
      checks: { "polly:a": "not-an-object" },
    });
    expect(errs).toHaveLength(1);
    expect(errs[0]).toContain("polly:a");
    expect(errs[0]).toContain("expected object");
  });

  test("flags configs that reference unknown check ids", () => {
    const errs = validateRunConfig(reg, {
      plugins: [],
      checks: { "polly:ghost": {} },
    });
    expect(errs).toHaveLength(1);
    expect(errs[0]).toContain("unknown check id");
  });
});

describe("runChecks", () => {
  test("runs every registered check when ids is undefined", async () => {
    const reg = registerPlugins([
      plugin("p", [trivialCheck("p:a"), trivialCheck("p:b"), trivialCheck("p:c")]),
    ]);
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    const report = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(report.ok).toBe(true);
    expect(report.results.map((r) => r.id).sort()).toEqual(["p:a", "p:b", "p:c"]);
    await rm(root, { recursive: true });
  });

  test("runs only the requested ids when given a list", async () => {
    const reg = registerPlugins([
      plugin("p", [trivialCheck("p:a"), trivialCheck("p:b"), trivialCheck("p:c")]),
    ]);
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    const report = await runChecks(reg, { plugins: [] }, ["p:a", "p:c"], { rootDir: root });
    expect(report.results.map((r) => r.id).sort()).toEqual(["p:a", "p:c"]);
    await rm(root, { recursive: true });
  });

  test("aggregate ok is false when any check fails", async () => {
    const reg = registerPlugins([
      plugin("p", [trivialCheck("p:ok", true), trivialCheck("p:bad", false, ["broken"])]),
    ]);
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    const report = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(report.ok).toBe(false);
    const bad = report.results.find((r) => r.id === "p:bad");
    expect(bad?.ok).toBe(false);
    expect(bad?.messages).toEqual(["broken"]);
    await rm(root, { recursive: true });
  });

  test("a check that throws is reported as a failure with error, no abort", async () => {
    const reg = registerPlugins([
      plugin("p", [
        trivialCheck("p:ok"),
        {
          id: "p:explodes",
          description: "throws",
          run: async () => {
            throw new Error("boom");
          },
        },
        trivialCheck("p:also-ok"),
      ]),
    ]);
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    const report = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(report.ok).toBe(false);
    const failed = report.results.find((r) => r.id === "p:explodes");
    expect(failed?.ok).toBe(false);
    expect(failed?.error).toBe("boom");
    // Other checks still ran
    expect(report.results.some((r) => r.id === "p:ok" && r.ok)).toBe(true);
    expect(report.results.some((r) => r.id === "p:also-ok" && r.ok)).toBe(true);
    await rm(root, { recursive: true });
  });

  test("cache hit on a second run skips the body", async () => {
    let runs = 0;
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    await writeFile(join(root, "in.txt"), "fixed");

    const check: Check<unknown> = {
      id: "p:cached",
      description: "counts runs",
      filesRead: () => [join(root, "in.txt")],
      run: async () => {
        runs++;
        return { ok: true, messages: [`ran ${runs} time(s)`] };
      },
    };
    const reg = registerPlugins([plugin("p", [check])]);

    const first = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(first.results[0]?.cached).toBe(false);
    expect(runs).toBe(1);

    const second = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(second.results[0]?.cached).toBe(true);
    expect(runs).toBe(1); // body did not run again

    await writeFile(join(root, "in.txt"), "different");
    const third = await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(third.results[0]?.cached).toBe(false);
    expect(runs).toBe(2); // input changed, body ran again

    await rm(root, { recursive: true });
  });

  test("--no-cache forces re-execution", async () => {
    let runs = 0;
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    await writeFile(join(root, "in.txt"), "fixed");
    const check: Check<unknown> = {
      id: "p:nocache",
      description: "",
      filesRead: () => [join(root, "in.txt")],
      run: async () => {
        runs++;
        return { ok: true, messages: [] };
      },
    };
    const reg = registerPlugins([plugin("p", [check])]);
    await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    await runChecks(reg, { plugins: [] }, undefined, { rootDir: root, noCache: true });
    expect(runs).toBe(2);
    await rm(root, { recursive: true });
  });

  test("failing outcomes are not cached", async () => {
    let runs = 0;
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    await writeFile(join(root, "in.txt"), "fixed");
    const check: Check<unknown> = {
      id: "p:fail",
      description: "",
      filesRead: () => [join(root, "in.txt")],
      run: async () => {
        runs++;
        return { ok: false, messages: ["nope"] };
      },
    };
    const reg = registerPlugins([plugin("p", [check])]);
    await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    await runChecks(reg, { plugins: [] }, undefined, { rootDir: root });
    expect(runs).toBe(2);
    await rm(root, { recursive: true });
  });

  test("unknown id raises", async () => {
    const reg = registerPlugins([plugin("p", [trivialCheck("p:a")])]);
    const root = await mkdtemp(join(tmpdir(), "polly-host-"));
    await expect(runChecks(reg, { plugins: [] }, ["p:ghost"], { rootDir: root })).rejects.toThrow(
      /Unknown check id/
    );
    await rm(root, { recursive: true });
  });
});

describe("listChecks", () => {
  test("returns sorted entries with id, description, and plugin name", () => {
    const reg = registerPlugins([
      plugin("z", [trivialCheck("z:b"), trivialCheck("z:a")]),
      plugin("a", [trivialCheck("a:x")]),
    ]);
    const list = listChecks(reg);
    expect(list.map((c) => c.id)).toEqual(["a:x", "z:a", "z:b"]);
    expect(list[0]?.plugin).toBe("a");
  });
});
