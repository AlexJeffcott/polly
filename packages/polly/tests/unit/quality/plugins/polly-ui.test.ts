import { describe, expect, test } from "bun:test";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pollyUiPlugin, registerPlugins, runChecks } from "@fairfox/polly/quality";

async function tmp(prefix: string): Promise<string> {
  return mkdtemp(join(tmpdir(), `${prefix}-`));
}

describe("pollyUiPlugin registration", () => {
  test("registers six namespaced checks under polly-ui", () => {
    const reg = registerPlugins([pollyUiPlugin]);
    for (const id of [
      "polly-ui:css-layout",
      "polly-ui:css-quality",
      "polly-ui:css-vars",
      "polly-ui:css-unused",
      "polly-ui:shared-components",
      "polly-ui:no-inline-handlers",
    ]) {
      expect(reg.has(id)).toBe(true);
    }
  });

  test("does not collide with pollyCorePlugin under the polly namespace", async () => {
    const { pollyCorePlugin } = await import("@fairfox/polly/quality");
    const reg = registerPlugins([pollyCorePlugin, pollyUiPlugin]);
    expect(reg.size).toBeGreaterThan(0);
    expect(reg.has("polly:no-as-casting")).toBe(true);
    expect(reg.has("polly-ui:css-vars")).toBe(true);
  });
});

describe("polly-ui:no-inline-handlers", () => {
  test("flags `onClick={fn}` in a .tsx file", async () => {
    const root = await tmp("polly-ui-nih-bad");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "comp.tsx"),
      `export function C() { return <button onClick={() => {}}>x</button>; }\n`
    );
    const reg = registerPlugins([pollyUiPlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyUiPlugin] },
      ["polly-ui:no-inline-handlers"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(false);
    expect(report.results[0]?.messages.some((m) => m.includes("onClick"))).toBe(true);
    await rm(root, { recursive: true });
  });

  test("passes a `data-action` attribute (the alternative)", async () => {
    const root = await tmp("polly-ui-nih-ok");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "comp.tsx"),
      `export function C() { return <button data-action="metric.create">x</button>; }\n`
    );
    const reg = registerPlugins([pollyUiPlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyUiPlugin] },
      ["polly-ui:no-inline-handlers"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test("allowedFiles glob exempts a path", async () => {
    const root = await tmp("polly-ui-nih-allow");
    await mkdir(join(root, "src", "legacy"), { recursive: true });
    await writeFile(
      join(root, "src", "legacy", "old.tsx"),
      `export function C() { return <button onClick={() => {}}>x</button>; }\n`
    );
    const reg = registerPlugins([pollyUiPlugin]);
    const report = await runChecks(
      reg,
      {
        plugins: [pollyUiPlugin],
        checks: { "polly-ui:no-inline-handlers": { allowedFiles: ["src/legacy/**"] } },
      },
      ["polly-ui:no-inline-handlers"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });

  test(".test.tsx files are excluded by default", async () => {
    const root = await tmp("polly-ui-nih-test");
    await mkdir(join(root, "src"), { recursive: true });
    await writeFile(
      join(root, "src", "comp.test.tsx"),
      `export function C() { return <button onClick={() => {}}>x</button>; }\n`
    );
    const reg = registerPlugins([pollyUiPlugin]);
    const report = await runChecks(
      reg,
      { plugins: [pollyUiPlugin] },
      ["polly-ui:no-inline-handlers"],
      { rootDir: root, noCache: true }
    );
    expect(report.results[0]?.ok).toBe(true);
    await rm(root, { recursive: true });
  });
});
