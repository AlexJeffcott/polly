import { afterAll, describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { findMutateConfigs, validateMutateTargets } from "../mutate-targets.ts";

const DEFINE = join(import.meta.dir, "../../../../mutate/src/define.ts");

const roots: string[] = [];
afterAll(() => {
  for (const root of roots) rmSync(root, { recursive: true, force: true });
});

function project(body?: string): string {
  const root = mkdtempSync(join(tmpdir(), "polly-mutate-targets-"));
  roots.push(root);
  mkdirSync(join(root, "src"));
  writeFileSync(join(root, "src/a.ts"), "export const a = 1;\n");
  if (body !== undefined) {
    writeFileSync(
      join(root, "polly.mutate.ts"),
      `import { defineMutation } from "${DEFINE}";\nexport default defineMutation(${body});\n`
    );
  }
  return root;
}

describe("polly.mutate.ts", () => {
  test("reads targets and tests.include, and reports each that resolves to no file", async () => {
    const root = project(
      '{ targets: ["src/a.ts", "src/gone.ts:1-2", "!src/x.ts"], tests: { include: ["t/*.ts"] } }'
    );
    const [entry] = await findMutateConfigs(root);
    expect(entry?.targets.patterns).toEqual(["src/a.ts", "src/gone.ts:1-2", "!src/x.ts"]);
    expect(entry?.tests.patterns).toEqual(["t/*.ts"]);
    const report = await validateMutateTargets(root);
    expect(report.issues.map((i) => [i.field, i.pattern])).toEqual([
      ["targets", "src/gone.ts:1-2"],
      ["tests.include", "t/*.ts"],
    ]);
  });

  test("a project without polly.mutate.ts has no configs and no issues", async () => {
    const root = project();
    expect(await validateMutateTargets(root)).toEqual({ configs: [], issues: [] });
  });

  test("a stryker.conf.json is not read", async () => {
    const root = project();
    writeFileSync(join(root, "stryker.conf.json"), JSON.stringify({ mutate: ["src/gone.ts"] }));
    expect(await findMutateConfigs(root)).toEqual([]);
  });
});
