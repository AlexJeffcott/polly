/**
 * pollyMutatePlugin through a real Bun.build: with the mutant variables set
 * the bundle carries the mutated text; without them it carries the original.
 */
import { afterAll, expect, test } from "bun:test";
import { pollyMutatePlugin } from "../engine/bundler-plugin.ts";
import { createFixtureProject } from "./fixture-project.ts";

const project = createFixtureProject("polly-mutate-bundle-", {
  "src/flag.ts": "export const positive = (a: number) => a > 0;\n",
  "src/page.ts": 'import { positive } from "./flag.ts";\nconsole.log(positive(1));\n',
});
afterAll(() => project.remove());

async function bundle(env: Record<string, string | undefined>): Promise<string> {
  const out = await Bun.build({
    entrypoints: [project.path("src/page.ts")],
    plugins: [pollyMutatePlugin(env)],
  });
  expect(out.success).toBe(true);
  return (await out.outputs[0]?.text()) ?? "";
}

test("the target's span is swapped in the bundle", async () => {
  const src = await Bun.file(project.path("src/flag.ts")).text();
  const start = src.indexOf("a > 0");
  const text = await bundle({
    POLLY_MUTATE_FILE: project.path("src/flag.ts"),
    POLLY_MUTATE_SPAN: JSON.stringify({ start, end: start + 5, replacement: "a >= 0" }),
  });
  expect(text).toContain("a >= 0");
});

test("without the variables the bundle is the original", async () => {
  const text = await bundle({});
  expect(text).toContain("a > 0");
  expect(text).not.toContain("a >= 0");
});
