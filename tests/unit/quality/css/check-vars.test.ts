import { mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { beforeEach, expect, test } from "bun:test";
import { checkCssVars } from "@fairfox/polly/quality";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-css-v-"));
});

test("passes when every var(--x) resolves to a definition", async () => {
  await writeFile(
    join(root, "theme.css"),
    `:root { --polly-text: #111; --polly-surface: #fff; }`,
  );
  await writeFile(
    join(root, "c.module.css"),
    `.x { color: var(--polly-text); background: var(--polly-surface); }`,
  );
  const r = await checkCssVars({ rootDir: root });
  expect(r.violations).toEqual([]);
});

test("flags an unknown var reference", async () => {
  await writeFile(
    join(root, "theme.css"),
    `:root { --polly-text: #111; }`,
  );
  await writeFile(
    join(root, "c.module.css"),
    `.x { color: var(--polly-text); background: var(--polly-surace); }`,
  );
  const r = await checkCssVars({ rootDir: root });
  expect(r.violations.length).toBe(1);
  expect(r.violations[0]?.content).toContain("--polly-surace");
});

test("dynamicVars are treated as defined", async () => {
  await writeFile(
    join(root, "theme.css"),
    `:root { --polly-text: #111; }`,
  );
  await writeFile(
    join(root, "c.module.css"),
    `.x { --runtime: var(--max-lines); color: var(--polly-text); }`,
  );
  const r = await checkCssVars({
    rootDir: root,
    dynamicVars: ["--max-lines"],
  });
  expect(r.violations).toEqual([]);
});

test("var references in TS files are also checked", async () => {
  await writeFile(
    join(root, "theme.css"),
    `:root { --polly-text: #111; }`,
  );
  await writeFile(
    join(root, "Comp.tsx"),
    `export const X = () => (<div style={{ color: 'var(--polly-missing)' }} />);`,
  );
  const r = await checkCssVars({ rootDir: root });
  expect(r.violations.length).toBe(1);
  expect(r.violations[0]?.content).toContain("--polly-missing");
});
