import { describe, expect, test } from "bun:test";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyCorePlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

describe("polly:relative-imports", () => {
  test("passes a `../foo` import (depth 1)", async () => {
    const root = await tmp("polly-ri-ok");
    await mkdir(join(root, "src", "a"), { recursive: true });
    await writeFile(join(root, "src", "a", "x.ts"), `import { y } from "../b";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:relative-imports"],
      {
        rootDir: root,
        noCache: true,
      }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("fails a `../../foo` import (depth 2 > default 1)", async () => {
    const root = await tmp("polly-ri-bad");
    await mkdir(join(root, "src", "a", "deep"), { recursive: true });
    await writeFile(join(root, "src", "a", "deep", "x.ts"), `import { y } from "../../b";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:relative-imports"],
      {
        rootDir: root,
        noCache: true,
      }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("../../b"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("`#src/foo` subpath imports always pass", async () => {
    const root = await tmp("polly-ri-subpath");
    await mkdir(join(root, "src", "a"), { recursive: true });
    await writeFile(join(root, "src", "a", "x.ts"), `import { y } from "#src/b";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:relative-imports"],
      {
        rootDir: root,
        noCache: true,
      }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("custom maxDepth allows deeper imports", async () => {
    const root = await tmp("polly-ri-cfg");
    await mkdir(join(root, "src", "a", "deep"), { recursive: true });
    await writeFile(join(root, "src", "a", "deep", "x.ts"), `import { y } from "../../b";\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:relative-imports": { maxDepth: 5 } },
      },
      ["polly:relative-imports"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:tsconfig-paths", () => {
  test("flags a tsconfig.json with paths set", async () => {
    const root = await tmp("polly-tcp-bad");
    await writeFile(
      join(root, "tsconfig.json"),
      JSON.stringify({ compilerOptions: { paths: { "@app/*": ["./src/*"] } } })
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:tsconfig-paths"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("@app/*"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("passes a tsconfig.json with no paths set", async () => {
    const root = await tmp("polly-tcp-ok");
    await writeFile(
      join(root, "tsconfig.json"),
      JSON.stringify({ compilerOptions: { strict: true } })
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:tsconfig-paths"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("allowedAliases skips opt-in alias names", async () => {
    const root = await tmp("polly-tcp-allow");
    await writeFile(
      join(root, "tsconfig.json"),
      JSON.stringify({ compilerOptions: { paths: { "@app/*": ["./src/*"] } } })
    );
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:tsconfig-paths": { allowedAliases: ["@app/*"] } },
      },
      ["polly:tsconfig-paths"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:no-raw-http", () => {
  test("default config is silent (no canonicalClient)", async () => {
    const root = await tmp("polly-nrh-default");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "f.ts"), `await fetch("https://example.com");\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:no-raw-http"], {
      rootDir: root,
      noCache: true,
    });
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("flags a fetch call when canonicalClient is configured", async () => {
    const root = await tmp("polly-nrh-bad");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(join(root, "src", "f.ts"), `await fetch("https://example.com");\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:no-raw-http": { canonicalClient: "#src/api/client" } },
      },
      ["polly:no-raw-http"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("fetch"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("allowedFiles glob exempts a path", async () => {
    const root = await tmp("polly-nrh-allow");
    await mkdir(join(root, "src", "legacy"), { recursive: true });
    await writeFile(join(root, "src", "legacy", "f.ts"), `await fetch("https://example.com");\n`);
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: {
          "polly:no-raw-http": {
            canonicalClient: "#src/api/client",
            allowedFiles: ["src/legacy/**"],
          },
        },
      },
      ["polly:no-raw-http"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});

describe("polly:types", () => {
  test("registers under polly:types with an actionable description", () => {
    const reg = registerPlugins([pollyCorePlugin]);
    const entry = reg.get("polly:types");
    expect(entry).toBeDefined();
    expect(entry?.check.description.toLowerCase()).toContain("tsc");
  });

  test("returns an informational message when no workspace packages match", async () => {
    const root = await tmp("polly-types-empty");
    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyCorePlugin],
        checks: { "polly:types": { workspaces: ["nonexistent-glob-*"] } },
      },
      ["polly:types"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    expect(report.results[0]?.messages.some((m) => m.includes("no workspace"))).toBe(true);
    await rm(root, { recursive: true });
  });
});
