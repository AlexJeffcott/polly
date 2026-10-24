// AnalysisSession lifecycle. An API that is never closed keeps Bun (and
// Node) alive forever, so the exit test runs a real subprocess, and a
// control run without close() shows the test can see the hang.

import { afterAll, describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { AnalysisSession, withAnalysisSession } from "../analysis-program";
import { TYPES_CORPUS } from "./corpus";

const MODULE = path.resolve(import.meta.dir, "../analysis-program.ts");
const scratch = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), "polly-session-"));

afterAll(() => {
  fs.rmSync(scratch, { recursive: true, force: true });
});

/** Run a script that opens the types corpus; resolve with its exit code, or "running" after `ms`. */
async function runScript(name: string, body: string, ms: number): Promise<number | "running"> {
  const file = path.join(scratch, `${name}.ts`);
  fs.writeFileSync(
    file,
    [
      `import { AnalysisSession, withAnalysisSession } from ${JSON.stringify(MODULE)};`,
      `const tsconfig = ${JSON.stringify(TYPES_CORPUS)};`,
      body,
      "",
    ].join("\n")
  );
  const child = Bun.spawn(["bun", file], { stdout: "ignore", stderr: "inherit" });
  const timer = new Promise<"running">((resolve) => setTimeout(() => resolve("running"), ms));
  const outcome = await Promise.race([child.exited, timer]);
  if (outcome === "running") child.kill();
  return outcome;
}

describe("AnalysisSession lifecycle", () => {
  test("a process exits once the session is closed", async () => {
    const code = await runScript(
      "closes",
      [
        "const session = new AnalysisSession();",
        "const program = await session.open(tsconfig);",
        "if (program.sourceFiles.length === 0) process.exitCode = 2;",
        "await session.close();",
      ].join("\n"),
      30_000
    );
    expect(code).toBe(0);
  }, 40_000);

  test("withAnalysisSession closes even when the callback throws", async () => {
    const code = await runScript(
      "throws",
      [
        "try {",
        "  await withAnalysisSession(async (session) => {",
        "    await session.open(tsconfig);",
        '    throw new Error("boom");',
        "  });",
        "} catch {",
        "  process.exitCode = 3;",
        "}",
      ].join("\n"),
      30_000
    );
    expect(code).toBe(3);
  }, 40_000);

  test("control: without close() the process does not exit", async () => {
    const code = await runScript(
      "leaks",
      ["const session = new AnalysisSession();", "await session.open(tsconfig);"].join("\n"),
      4_000
    );
    expect(code).toBe("running");
  }, 20_000);

  test("open is cached per tsconfig, openIsolated is not, and a closed session refuses", async () => {
    const session = new AnalysisSession();
    try {
      const [a, b] = await Promise.all([
        session.open(TYPES_CORPUS),
        session.open(path.relative(process.cwd(), TYPES_CORPUS)),
      ]);
      expect(a).toBe(b);
      const isolated = await session.openIsolated(TYPES_CORPUS);
      expect(isolated).not.toBe(a);
      expect(isolated.sourceFiles.map((f) => f.fileName)).toEqual(
        a.sourceFiles.map((f) => f.fileName)
      );
    } finally {
      await session.close();
    }
    await session.close();
    await expect(session.open(TYPES_CORPUS)).rejects.toThrow(/closed/);
    await expect(session.openIsolated(TYPES_CORPUS)).rejects.toThrow(/closed/);
  }, 60_000);

  test("a missing tsconfig rejects without starting the API", async () => {
    await withAnalysisSession(async (session) => {
      await expect(session.open(path.join(scratch, "no-such", "tsconfig.json"))).rejects.toThrow(
        /File not found/
      );
    });
  });
});
