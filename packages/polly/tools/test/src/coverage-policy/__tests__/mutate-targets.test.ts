import { afterAll, describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { findMutateConfigs, validateMutateTargets } from "../mutate-targets.ts";

const roots: string[] = [];
afterAll(() => {
  for (const root of roots) rmSync(root, { recursive: true, force: true });
});

function project(config: unknown): string {
  const root = mkdtempSync(join(tmpdir(), "polly-mutate-targets-"));
  roots.push(root);
  mkdirSync(join(root, "src"));
  writeFileSync(join(root, "src/a.ts"), "export const a = 1;\n");
  writeFileSync(join(root, "stryker.conf.json"), JSON.stringify(config));
  return root;
}

describe("Stryker configs", () => {
  test("reads mutate and the bun runner's testFiles", async () => {
    const root = project({ mutate: ["src/a.ts", "src/gone.ts"], bun: { testFiles: ["t/*.ts"] } });
    const [entry] = await findMutateConfigs(root);
    expect(entry?.targets.patterns).toEqual(["src/a.ts", "src/gone.ts"]);
    expect(entry?.tests.patterns).toEqual(["t/*.ts"]);
    const report = await validateMutateTargets(root);
    expect(report.issues.map((i) => i.pattern)).toEqual(["src/gone.ts", "t/*.ts"]);
  });

  test("a path list that is not an array of strings throws, naming the field", async () => {
    const root = project({ mutate: "src/a.ts" });
    await expect(findMutateConfigs(root)).rejects.toThrow("`mutate` is not an array of strings");
  });
});
