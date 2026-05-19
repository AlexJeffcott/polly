import { describe, expect, test } from "bun:test";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyCorePlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

describe("polly:boundaries (directional zone bans)", () => {
  test("passes when src/ does not import from tools/", async () => {
    const root = await tmp("polly-boundaries-clean");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "ok.ts"), `export const x = 1;\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:boundaries"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("fails when src/ imports from tools/", async () => {
    const root = await tmp("polly-boundaries-bad");
    await mkdir(join(root, "src"), { recursive: true });
    await mkdir(join(root, "tools", "verify"), { recursive: true });
    await writeFile(join(root, "tools", "verify", "v.ts"), `export const v = 1;\n`);
    await writeFile(join(root, "src", "bad.ts"), `import { v } from "../tools/verify/v";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:boundaries"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("src") && m.includes("tools/"))).toBe(
      true
    );
    await rm(root, { recursive: true });
  });

  test("test files are excluded from zone scanning", async () => {
    const root = await tmp("polly-boundaries-test");
    await mkdir(join(root, "src"), { recursive: true });
    await mkdir(join(root, "tools"), { recursive: true });
    await writeFile(join(root, "tools", "v.ts"), `export const v = 1;\n`);
    await writeFile(join(root, "src", "thing.test.ts"), `import { v } from "../tools/v";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:boundaries"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:server-imports", () => {
  test("passes when browser code uses no server-only imports", async () => {
    const root = await tmp("polly-server-imports-clean");
    await mkdir(join(root, "src", "popup"), { recursive: true });
    await writeFile(join(root, "src", "popup", "ui.ts"), `import { x } from "./other";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:server-imports"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("fails when browser code imports node:fs", async () => {
    const root = await tmp("polly-server-imports-bad");
    await mkdir(join(root, "src", "popup"), { recursive: true });
    await writeFile(
      join(root, "src", "popup", "bad.ts"),
      `import fs from "node:fs";\nexport const f = fs;\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:server-imports"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("bad.ts"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("non-browser packages are not scanned", async () => {
    const root = await tmp("polly-server-imports-nonbrowser");
    await mkdir(join(root, "tools", "v"), { recursive: true });
    // tools/v is NOT in the default browserPaths list, so node:fs is fine.
    await writeFile(
      join(root, "tools", "v", "v.ts"),
      `import fs from "node:fs";\nexport const f = fs;\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:server-imports"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("per-check config can override browserPaths and bannedSpecifiers", async () => {
    const root = await tmp("polly-server-imports-cfg");
    await mkdir(join(root, "custom-browser-zone"), { recursive: true });
    await writeFile(
      join(root, "custom-browser-zone", "bad.ts"),
      `import { x } from "forbidden-module";\n`
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: {
          "polly:server-imports": {
            browserPaths: ["custom-browser-zone"],
            bannedSpecifiers: ["forbidden-module"],
          },
        },
      },
      ["polly:server-imports"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    await rm(root, { recursive: true });
  });
});

describe("polly:security (semgrep wrapper)", () => {
  test("registers under polly:security with an actionable description", () => {
    const reg = registerPlugins([pollyCorePlugin]);
    const entry = reg.get("polly:security");
    expect(entry).toBeDefined();
    expect(entry?.check.description.toLowerCase()).toContain("semgrep");
  });

  // Behavioural coverage: in CI semgrep is installed via Brewfile, so a
  // run against an empty tree exits cleanly. A missing-tool path is
  // exercised when consumers run on a host without semgrep, where the
  // wrapper returns ok=false with the install instructions surfaced. We
  // do not assert the missing-tool path here because mocking PATH is
  // not portable across platforms; the install-instructions string is
  // covered by inspection of the wrap source.
});
