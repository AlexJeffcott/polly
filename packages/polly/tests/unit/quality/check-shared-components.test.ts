/**
 * Unit test for @fairfox/polly/quality's checkSharedComponents.
 *
 * Builds a fake package tree in a tmp directory, plants .tsx files
 * with raw HTML elements that should be banned (and a few that should
 * not), runs the check, and asserts the violation list.
 *
 * Covers:
 *   - every element in the default rule set (<button>, <input>,
 *     <textarea>, <select>, <form>, <dialog>)
 *   - the <input type="hidden"> skip predicate
 *   - the "exempt packages" escape hatch
 *   - a consumer-supplied `additionalRules` entry
 *   - commented-out elements being ignored
 */

import { beforeEach, expect, test } from "bun:test";
import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkSharedComponents } from "@fairfox/polly/quality";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-shared-components-"));
});

async function plant(relPath: string, text: string): Promise<void> {
  const abs = join(root, relPath);
  await mkdir(join(abs, ".."), { recursive: true });
  await writeFile(abs, text);
}

test("flags every default-rule element", async () => {
  await plant(
    "packages/app/src/App.tsx",
    `
    export function App() {
      return (
        <div>
          <button>Click</button>
          <input type="text" />
          <textarea />
          <select />
          <form action="/x" />
          <dialog open />
        </div>
      );
    }
    `.trim()
  );
  const result = await checkSharedComponents({ root });
  const elements = result.violations.map((v) => v.element).sort();
  expect(elements).toEqual(["<button>", "<dialog>", "<form>", "<input>", "<select>", "<textarea>"]);
});

test("skips <input type='hidden'>", async () => {
  await plant(
    "packages/app/src/App.tsx",
    `
    export function App() {
      return <input type="hidden" value="csrf" />;
    }
    `.trim()
  );
  const result = await checkSharedComponents({ root });
  expect(result.violations).toEqual([]);
});

test("exempts named packages", async () => {
  await plant("packages/legacy/src/Legacy.tsx", `export const X = () => <button />;`);
  await plant("packages/fresh/src/Fresh.tsx", `export const Y = () => <button />;`);
  const result = await checkSharedComponents({
    root,
    exemptPackages: new Set(["legacy"]),
  });
  expect(result.violations.map((v) => v.file)).toEqual(["packages/fresh/src/Fresh.tsx"]);
});

test("accepts additional consumer rules", async () => {
  await plant(
    "packages/app/src/App.tsx",
    `
    export const X = () => <marquee>scroll</marquee>;
    `.trim()
  );
  const result = await checkSharedComponents({
    root,
    additionalRules: [
      { pattern: /<marquee[\s>]/, element: "<marquee>", replacement: "<ScrollingText>" },
    ],
  });
  expect(result.violations).toHaveLength(1);
  expect(result.violations[0]?.element).toBe("<marquee>");
});

test("ignores commented-out elements", async () => {
  await plant(
    "packages/app/src/App.tsx",
    `
    export function App() {
      // <button>old</button>
      return null;
    }
    `.trim()
  );
  const result = await checkSharedComponents({ root });
  expect(result.violations).toEqual([]);
});

test("skips dotted dirs in the traversal default", async () => {
  await plant("packages/app/dist/build.tsx", `export const X = () => <button />;`);
  await plant("packages/app/node_modules/foo.tsx", `export const X = () => <button />;`);
  await plant("packages/app/src/App.tsx", `export const X = () => <div>ok</div>;`);
  const result = await checkSharedComponents({ root });
  expect(result.violations).toEqual([]);
});

test("print() summarises violations through the supplied log sink", async () => {
  await plant("packages/app/src/App.tsx", `export const X = () => <button />;`);
  const result = await checkSharedComponents({ root });
  const captured: string[] = [];
  result.print((m) => captured.push(m));
  expect(captured.some((line) => line.includes("1 violation(s)"))).toBe(true);
  expect(captured.some((line) => line.includes("<button>"))).toBe(true);
});
