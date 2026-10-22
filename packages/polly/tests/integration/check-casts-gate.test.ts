/**
 * The cast gate (`scripts/check-casts.ts`) run as a subprocess against a
 * throwaway project: one tsgo session per run, real probe rewrites, real
 * baseline file. Each fixture cast pins one verdict of the policy.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";

const SCRIPT = resolve(import.meta.dir, "../../scripts/check-casts.ts");

const FIXTURE = `interface A { a: number }
interface B { b: string }
declare const a: A;
declare const u: unknown;
function take(x: A): number { return x.a; }

export const single = u as A;
take({ a: 1 } as unknown as A);
const widened = a as unknown as A & { extra: string };
take(widened);
widened.extra.toUpperCase();
const parsed = JSON.parse("{}") as unknown as A;
take(parsed);
const unexplained = a as unknown as B;
unexplained.b.toUpperCase();
// cast: B-shaped view of an A, for the fixture
const explained = a as unknown as B;
explained.b.toUpperCase();
export const literal = "x" as const;
// prose that says a as b is not a cast
`;

interface Finding {
  text: string;
  kind: string;
  probe?: string;
  blocked?: string;
  status: string;
}

let dir = "";

function writeFixture(source: string): void {
  writeFileSync(join(dir, "fixture.ts"), source);
}

async function gate(...flags: string[]): Promise<{ code: number; findings: Finding[] }> {
  const proc = Bun.spawn(["bun", SCRIPT, "--root", dir, "--json", ...flags], {
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, code] = await Promise.all([new Response(proc.stdout).text(), proc.exited]);
  const parsed: unknown = JSON.parse(out);
  const findings =
    typeof parsed === "object" &&
    parsed !== null &&
    "findings" in parsed &&
    Array.isArray(parsed.findings)
      ? parsed.findings.filter(
          (f: unknown): f is Finding =>
            typeof f === "object" && f !== null && "text" in f && "status" in f
        )
      : [];
  return { code, findings };
}

function byText(findings: Finding[], start: string): Finding | undefined {
  return findings.find((f) => f.text.startsWith(start));
}

beforeAll(() => {
  dir = mkdtempSync(join(tmpdir(), "polly-check-casts-"));
  writeFileSync(
    join(dir, "tsconfig.json"),
    JSON.stringify({
      compilerOptions: { strict: true, noEmit: true, lib: ["ESNext"], target: "ESNext" },
    })
  );
});

afterAll(() => {
  rmSync(dir, { recursive: true, force: true });
});

describe("check-casts gate", () => {
  test("classifies each cast by what the compiler needs", async () => {
    writeFixture(FIXTURE);
    const { code, findings } = await gate();
    expect(code).toBe(1);
    expect(findings).toHaveLength(6);
    expect(byText(findings, "u as A")).toMatchObject({
      kind: "single",
      probe: "required",
      status: "violation",
    });
    expect(byText(findings, "{ a: 1 } as unknown as A")).toMatchObject({
      probe: "removable",
      status: "violation",
    });
    expect(byText(findings, "a as unknown as A & { extra: string }")).toMatchObject({
      probe: "comparable",
      status: "violation",
    });
    // An `any` operand fits every target, so removing its cast loses the type without an error.
    expect(byText(findings, 'JSON.parse("{}") as unknown as A')).toMatchObject({
      blocked: "opaque-operand",
      status: "violation",
    });
    const incomparable = findings.filter((f) => f.text === "a as unknown as B");
    expect(incomparable.map((f) => [f.probe, f.status])).toEqual([
      ["incomparable", "violation"],
      ["incomparable", "allowed"],
    ]);
  }, 30_000);

  // With the compiler silenced every rewrite compiles, so the probe would call each cast removable.
  test("does not probe a cast the compiler does not check", async () => {
    writeFixture(
      `// @ts-nocheck\ninterface A { a: number }\nconst v: unknown = 1;\nexport const n = v as A;\n`
    );
    const nocheck = await gate("--fix");
    expect(byText(nocheck.findings, "v as A")).toMatchObject({
      blocked: "unchecked",
      status: "violation",
    });
    expect(readFileSync(join(dir, "fixture.ts"), "utf-8")).toContain("v as A");

    writeFixture(
      `interface A { a: number }\nconst v: unknown = 1;\n// @ts-expect-error unrelated\nexport const n: string = v as A;\n`
    );
    const suppressed = await gate();
    expect(byText(suppressed.findings, "v as A")).toMatchObject({ blocked: "unchecked" });
  }, 30_000);

  test("the baseline admits recorded casts and flags only new ones", async () => {
    writeFixture(FIXTURE);
    expect((await gate("--update")).code).toBe(0);
    const clean = await gate();
    expect(clean.code).toBe(0);
    expect(clean.findings.filter((f) => f.status === "baselined")).toHaveLength(5);

    writeFixture(`${FIXTURE}export const added = u as B;\n`);
    const added = await gate();
    expect(added.code).toBe(1);
    expect(added.findings.filter((f) => f.status === "violation").map((f) => f.text)).toEqual([
      "u as B",
    ]);
    rmSync(join(dir, "casts-baseline.json"));
  }, 60_000);

  test("--fix deletes only the removable cast", async () => {
    writeFixture(FIXTURE);
    expect((await gate("--fix")).code).toBe(0);
    const fixed = readFileSync(join(dir, "fixture.ts"), "utf-8");
    expect(fixed).toContain("take({ a: 1 });");
    expect(fixed).toContain('JSON.parse("{}") as unknown as A');
    expect(fixed).toContain("a as unknown as A & { extra: string }");
  }, 30_000);
});
