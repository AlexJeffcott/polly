/**
 * `requires` / `ensures` under POLLY_CONTRACTS. The mode is read once at
 * module load, so each mode gets its own Bun process on a fixture that calls
 * both primitives with a false condition and prints what happened.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mkdtempSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";

const PRIMITIVES = resolve(import.meta.dir, "../primitives/index.ts");

let dir: string;
let script: string;

beforeAll(() => {
  dir = realpathSync(mkdtempSync(join(tmpdir(), "polly-contracts-runtime-")));
  script = join(dir, "calls.ts");
  writeFileSync(
    script,
    [
      `import { contractsMode, drainContractViolations, ensures, requires } from ${JSON.stringify(PRIMITIVES)};`,
      'const out: string[] = ["mode:" + contractsMode()];',
      'for (const [name, fn] of [["requires", requires], ["ensures", ensures]] as const) {',
      "  try {",
      '    fn(false, "must hold");',
      '    out.push(name + ":ok");',
      "  } catch (e) {",
      '    out.push(name + ":" + (e as Error).name + ":" + (e as Error).message);',
      "  }",
      "}",
      'out.push("drained:" + drainContractViolations().length);',
      'out.push("drained-again:" + drainContractViolations().length);',
      'console.log(out.join("\\n"));',
    ].join("\n")
  );
});
afterAll(() => rmSync(dir, { recursive: true, force: true }));

const CALL_LINE = 5;

async function runWith(mode: string | undefined): Promise<string[]> {
  const env = { ...process.env };
  delete env["POLLY_CONTRACTS"];
  if (mode !== undefined) env["POLLY_CONTRACTS"] = mode;
  const proc = Bun.spawn(["bun", script], { env, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr, code] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  if (code !== 0) throw new Error(`fixture exited ${code}: ${stderr}`);
  return stdout.trim().split("\n");
}

describe("POLLY_CONTRACTS", () => {
  test("unset: both primitives are no-ops and record nothing", async () => {
    expect(await runWith(undefined)).toEqual([
      "mode:off",
      "requires:ok",
      "ensures:ok",
      "drained:0",
      "drained-again:0",
    ]);
  });

  test("an unknown value is off", async () => {
    expect((await runWith("yes"))[0]).toBe("mode:off");
  });

  test("ensures: a false postcondition throws a ContractViolation naming the call site; requires stays inert", async () => {
    const lines = await runWith("ensures");
    expect(lines[0]).toBe("mode:ensures");
    expect(lines[1]).toBe("requires:ok");
    expect(lines[2]).toBe(
      `ensures:ContractViolation:[polly-contract ensures ${script}:${CALL_LINE}] must hold`
    );
    expect(lines[3]).toBe("drained:1");
    expect(lines[4]).toBe("drained-again:0");
  });

  test("all: both throw, and each violation is recorded for a harness to drain", async () => {
    const lines = await runWith("all");
    expect(lines[1]).toBe(
      `requires:ContractViolation:[polly-contract requires ${script}:${CALL_LINE}] must hold`
    );
    expect(lines[2]).toBe(
      `ensures:ContractViolation:[polly-contract ensures ${script}:${CALL_LINE}] must hold`
    );
    expect(lines[3]).toBe("drained:2");
  });
});
