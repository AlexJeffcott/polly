import { beforeEach, expect, test } from "bun:test";
import { mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkCssUnused } from "@fairfox/polly/quality";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "polly-css-u-"));
});

test("flags a class with no TS reference", async () => {
  await writeFile(
    join(root, "Card.module.css"),
    `.container { color: red; }
.unused { color: blue; }`
  );
  await writeFile(
    join(root, "Card.tsx"),
    `import styles from "./Card.module.css"; export const X = () => <div className={styles.container} />;`
  );
  const r = await checkCssUnused({ rootDir: root });
  expect(r.violations.length).toBe(1);
  expect(r.violations[0]?.content).toBe(".unused");
});

test("alwaysUsedClasses silences the report for a named class", async () => {
  await writeFile(join(root, "Card.module.css"), `.dynamic { color: red; }`);
  await writeFile(join(root, "Card.tsx"), `export const X = () => null;`);
  const r = await checkCssUnused({
    rootDir: root,
    alwaysUsedClasses: ["dynamic"],
  });
  expect(r.violations).toEqual([]);
});

test("passes when every class is referenced from TSX", async () => {
  await writeFile(
    join(root, "Card.module.css"),
    `.a { color: red; }
.b { color: blue; }`
  );
  await writeFile(
    join(root, "Card.tsx"),
    `import s from "./Card.module.css"; export const X = () => <div className={s.a + " " + s.b} />;`
  );
  const r = await checkCssUnused({ rootDir: root });
  expect(r.violations).toEqual([]);
});

test("flags a locally-defined variable with no reference", async () => {
  await writeFile(
    join(root, "Card.module.css"),
    `.c {
  --card-local: 10px;
  padding: 2px;
}`
  );
  const r = await checkCssUnused({ rootDir: root });
  expect(r.violations.some((v) => v.content === "--card-local")).toBe(true);
});
