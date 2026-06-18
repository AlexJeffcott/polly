import { describe, expect, test } from "bun:test";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkNoFixedWaits, scanText } from "../../tools/quality/src/no-fixed-waits";

describe("scanText — flagged sleeps", () => {
  test("page.waitForTimeout", () => {
    expect(scanText("await page.waitForTimeout(500);")).toHaveLength(1);
  });
  test("Bun.sleep", () => {
    expect(scanText("await Bun.sleep(100);")).toHaveLength(1);
  });
  test("setTimeout resolving a promise (named resolve)", () => {
    expect(scanText("await new Promise((resolve) => setTimeout(resolve, 50));")).toHaveLength(1);
  });
  test("setTimeout resolving a promise (short name)", () => {
    expect(scanText("await new Promise((r) => setTimeout(r, 50));")).toHaveLength(1);
  });
});

describe("scanText — legitimate timers pass", () => {
  test("setTimeout with a real callback (debounce)", () => {
    expect(scanText("setTimeout(() => flush(state), 200);")).toHaveLength(0);
  });
  test("setTimeout with a recursive poll step", () => {
    expect(scanText("setTimeout(pollOnce, intervalMs);")).toHaveLength(0);
  });
  test("a commented-out sleep is ignored", () => {
    expect(scanText("// await Bun.sleep(100);")).toHaveLength(0);
  });
  test("waitForTimeout inside a string is ignored", () => {
    expect(scanText("const doc = 'call page.waitForTimeout(n) to pause'; // note")).toHaveLength(0);
  });
});

describe("checkNoFixedWaits — integration", () => {
  function fixture(files: Record<string, string>): string {
    const dir = mkdtempSync(join(tmpdir(), "no-fixed-waits-"));
    for (const [name, content] of Object.entries(files)) {
      writeFileSync(join(dir, name), content);
    }
    return dir;
  }

  test("flags sleeps across files", async () => {
    const dir = fixture({
      "a.ts": "await Bun.sleep(10);\n",
      "b.ts": "await new Promise((resolve) => setTimeout(resolve, 5));\n",
      "ok.ts": "setTimeout(() => doWork(), 10);\n",
    });
    const { violations } = await checkNoFixedWaits({ rootDir: dir });
    expect(violations.map((v) => v.file).sort()).toEqual(["a.ts", "b.ts"]);
  });

  test("excludeFiles skips blessed delay primitives", async () => {
    const dir = fixture({
      "timers.ts": "export const sleep = (ms) => new Promise((r) => setTimeout(r, ms));\n",
    });
    const all = await checkNoFixedWaits({ rootDir: dir });
    expect(all.violations).toHaveLength(1);
    const scoped = await checkNoFixedWaits({ rootDir: dir, excludeFiles: ["timers.ts"] });
    expect(scoped.violations).toHaveLength(0);
  });
});
