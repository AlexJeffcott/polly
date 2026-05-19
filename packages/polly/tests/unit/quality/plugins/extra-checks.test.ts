import { describe, expect, test } from "bun:test";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyCorePlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

describe("polly:forbidden-deps", () => {
  test("flags an import of a banned package", async () => {
    const root = await tmp("polly-fd-bad");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "uses-vitest.ts"), `import { test } from "vitest";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:forbidden-deps"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("vitest"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("passes a clean tree", async () => {
    const root = await tmp("polly-fd-clean");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "ok.ts"), `import { test } from "bun:test";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:forbidden-deps"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("test files are excluded", async () => {
    const root = await tmp("polly-fd-test");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "thing.test.ts"), `import { mock } from "vitest";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:forbidden-deps"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("custom banned list overrides defaults", async () => {
    const root = await tmp("polly-fd-cfg");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "uses-foo.ts"), `import { x } from "forbidden-pkg";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: {
          "polly:forbidden-deps": {
            banned: { "Custom rule": ["forbidden-pkg"] },
          },
        },
      },
      ["polly:forbidden-deps"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("Custom rule"))).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-state-hooks", () => {
  test("flags useState calls", async () => {
    const root = await tmp("polly-nsh-bad");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "comp.tsx"),
      `import { useState } from "react";\nconst [n, setN] = useState(0);\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:no-state-hooks"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("useState"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("passes when no banned hooks are used", async () => {
    const root = await tmp("polly-nsh-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "ok.ts"),
      `import { signal } from "@preact/signals";\nexport const s = signal(0);\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:no-state-hooks"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("allowedFiles glob exempts a path", async () => {
    const root = await tmp("polly-nsh-allow");
    await mkdir(join(root, "src", "legacy"), { recursive: true });
    await writeFile(
      join(root, "src", "legacy", "old.tsx"),
      `import { useReducer } from "react";\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:no-state-hooks": { allowedFiles: ["src/legacy/**"] } },
      },
      ["polly:no-state-hooks"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:typographic-quotes", () => {
  test("default config is silent", async () => {
    const root = await tmp("polly-tq-default");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "any.ts"), `const a = 'hi';\nconst b = '“hi”';\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:typographic-quotes"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("typographicZone fails on straight quotes", async () => {
    const root = await tmp("polly-tq-tz");
    await mkdir(join(root, "src", "i18n"), { recursive: true });
    await writeFile(join(root, "src", "i18n", "strings.ts"), `export const greet = 'hi';\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: {
          "polly:typographic-quotes": { typographicZone: ["src/i18n/**"] },
        },
      },
      ["polly:typographic-quotes"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("straight quote"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("straightZone fails on typographic quotes", async () => {
    const root = await tmp("polly-tq-sz");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "code.ts"), `const a = ‘hi’;\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:typographic-quotes": { straightZone: ["src/**"] } },
      },
      ["polly:typographic-quotes"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("typographic quote"))).toBe(true);
    await rm(root, { recursive: true });
  });
});
