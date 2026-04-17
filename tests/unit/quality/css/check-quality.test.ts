import { beforeEach, expect, test } from "bun:test";
import { mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkCssQuality } from "@fairfox/polly/quality";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-css-q-"));
});

async function writeCss(name: string, content: string): Promise<void> {
  await writeFile(join(root, name), content);
}

test("passes when every value uses a semantic token", async () => {
  await writeCss(
    "ok.module.css",
    `.box {
  color: var(--polly-text);
  background: var(--polly-surface);
  z-index: var(--polly-z-overlay);
  border-radius: var(--polly-radius-md);
  font-weight: var(--polly-weight-bold);
}`
  );
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations).toEqual([]);
});

test("flags hardcoded hex colours", async () => {
  await writeCss("bad.module.css", `.x { color: #ff0000; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations.map((v) => v.rule)).toContain("no-hardcoded-color");
});

test("flags !important", async () => {
  await writeCss("bad.module.css", `.x { color: red !important; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations.some((v) => v.rule === "no-important")).toBe(true);
});

test("flags numeric font-weight", async () => {
  await writeCss("bad.module.css", `.x { font-weight: 700; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations.some((v) => v.rule === "no-hardcoded-font-weight")).toBe(true);
});

test("flags rem units outside calc()", async () => {
  await writeCss("bad.module.css", `.x { padding: 1rem; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations.some((v) => v.rule === "no-rem-units")).toBe(true);
});

test("flags hardcoded border-radius", async () => {
  await writeCss("bad.module.css", `.x { border-radius: 8px; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations.some((v) => v.rule === "no-hardcoded-border-radius")).toBe(true);
});

test("skips files with polly-ignore-all on line 1", async () => {
  await writeCss(
    "ignored.module.css",
    `/* polly-ignore-all */
.x { color: red; font-weight: 900; }`
  );
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations).toEqual([]);
});

test("honours disableRules option", async () => {
  await writeCss("partial.module.css", `.x { color: #333; font-weight: 700; }`);
  const result = await checkCssQuality({
    rootDir: root,
    disableRules: ["no-hardcoded-color"],
  });
  expect(result.violations.some((v) => v.rule === "no-hardcoded-color")).toBe(false);
  expect(result.violations.some((v) => v.rule === "no-hardcoded-font-weight")).toBe(true);
});

test("theme.css is skipped by default (defines raw values)", async () => {
  await writeCss("theme.css", `:root { --polly-text: #111; --polly-surface: #fff; }`);
  const result = await checkCssQuality({ rootDir: root });
  expect(result.violations).toEqual([]);
});
