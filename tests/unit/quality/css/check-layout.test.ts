import { beforeEach, expect, test } from "bun:test";
import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkCssLayout } from "@fairfox/polly/quality";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-css-l-"));
});

async function writeFileAt(path: string, content: string): Promise<void> {
  const full = join(root, path);
  const dir = full.substring(0, full.lastIndexOf("/"));
  await mkdir(dir, { recursive: true });
  await writeFile(full, content);
}

test("flags display: flex in a non-Layout CSS module", async () => {
  await writeFileAt("components/Card.module.css", `.x { display: flex; }`);
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations.length).toBe(1);
  expect(r.violations[0]?.rule).toContain("flex");
});

test("flags display: grid in a non-Layout CSS module", async () => {
  await writeFileAt("components/Card.module.css", `.x { display: grid; }`);
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations[0]?.rule).toContain("grid");
});

test("exempts Layout.module.css", async () => {
  await writeFileAt("ui/Layout.module.css", `.layout { display: grid; }`);
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations).toEqual([]);
});

test("exempts a line suppressed by /* layout-ignore */ on the same line", async () => {
  await writeFileAt("components/Card.module.css", `.x { display: flex; /* layout-ignore */ }`);
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations).toEqual([]);
});

test("exempts a line suppressed by /* layout-ignore */ on the preceding line", async () => {
  await writeFileAt(
    "components/Card.module.css",
    `/* layout-ignore */
.x { display: flex; }`
  );
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations).toEqual([]);
});

test("flags inline display: 'flex' in TSX", async () => {
  await writeFileAt(
    "components/Card.tsx",
    `export const X = () => <div style={{ display: "flex" }} />;`
  );
  const r = await checkCssLayout({ rootDir: root });
  expect(r.violations.length).toBe(1);
  expect(r.violations[0]?.rule).toContain("inline");
});

test("custom layoutExemptPaths is honoured", async () => {
  await writeFileAt("components/MyStack.module.css", `.stack { display: flex; }`);
  const r = await checkCssLayout({
    rootDir: root,
    layoutExemptPaths: ["MyStack.module.css"],
  });
  expect(r.violations).toEqual([]);
});
