import { describe, expect, test } from "bun:test";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyCorePlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

describe("pollyCorePlugin", () => {
  test("registers four namespaced core checks", () => {
    const reg = registerPlugins([pollyCorePlugin]);
    expect(reg.has("polly:no-as-casting")).toBe(true);
    expect(reg.has("polly:no-require")).toBe(true);
    expect(reg.has("polly:secrets")).toBe(true);
    expect(reg.has("polly:gitignore-cross-check")).toBe(true);
  });

  test("polly:no-as-casting passes a clean fixture and fails a dirty one", async () => {
    const reg = registerPlugins([pollyCorePlugin]);

    const clean = await tmp("polly-core-clean");
    await writeFile(join(clean, "ok.ts"), "export const x: unknown = 1;\n");
    const cleanReport = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:no-as-casting"],
      { rootDir: clean, noCache: true }
    );
    expect(cleanReport.results[0]?.ok).toBe(true);

    const dirty = await tmp("polly-core-dirty");
    await writeFile(dirty + "/bad.ts", "const y = foo as Bar;\n");
    const dirtyReport = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:no-as-casting"],
      { rootDir: dirty, noCache: true }
    );
    expect(dirtyReport.results[0]?.ok).toBe(false);
    expect(dirtyReport.results[0]?.messages.some((m) => m.includes("bad.ts"))).toBe(true);

    await rm(clean, { recursive: true });
    await rm(dirty, { recursive: true });
  });

  test("polly:no-require passes a clean fixture and fails a dirty one", async () => {
    const reg = registerPlugins([pollyCorePlugin]);

    const clean = await tmp("polly-core-clean");
    await writeFile(join(clean, "ok.ts"), `import { x } from "./other";\n`);
    const cleanReport = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:no-require"], {
      rootDir: clean,
      noCache: true,
    });
    expect(cleanReport.results[0]?.ok).toBe(true);

    const dirty = await tmp("polly-core-dirty");
    await writeFile(join(dirty, "bad.ts"), `const fs = require("node:fs");\n`);
    const dirtyReport = await runChecks(reg, { plugins: [pollyCorePlugin] }, ["polly:no-require"], {
      rootDir: dirty,
      noCache: true,
    });
    expect(dirtyReport.results[0]?.ok).toBe(false);

    await rm(clean, { recursive: true });
    await rm(dirty, { recursive: true });
  });

  test("polly:gitignore-cross-check passes when allowlisted paths are gitignored", async () => {
    const root = await tmp("polly-core-gitignore");
    await writeFile(
      join(root, ".gitleaks.toml"),
      `[allowlist]
# Gitignored files
paths = [
  '''.env\\.local$''',
]
`
    );
    await writeFile(join(root, ".gitignore"), ".env.local\n");

    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:gitignore-cross-check"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("polly:gitignore-cross-check fails when allowlisted path is missing from .gitignore", async () => {
    const root = await tmp("polly-core-gitignore-bad");
    await writeFile(
      join(root, ".gitleaks.toml"),
      `[allowlist]
# Gitignored files
paths = [
  '''secret\\.env$''',
]
`
    );
    await writeFile(join(root, ".gitignore"), "node_modules\n");

    const reg = registerPlugins([pollyCorePlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyCorePlugin] },
      ["polly:gitignore-cross-check"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("secret.env"))).toBe(true);
    await rm(root, { recursive: true });
  });
});
