/**
 * Contracts as a kill oracle, end to end: real `bun test` processes, the
 * real verify primitives (imported by absolute path, never a shim), matrix
 * mode so kills are attributed.
 *
 *   account.ts  a handler whose only check on the role it sets is an
 *               `ensures`; its test asserts only `loggedIn`. The handler
 *               swallows the throw, as the message bus does, so the kill
 *               must come from the preload's afterEach drain. Contracts off:
 *               the `||` → `&&` mutant survives. Contracts on: it is killed,
 *               attributed to the ensures site, and marked contract-only.
 *   session.ts  a test that drives `close()` from a cold state, against its
 *               `requires`. Under `all` the baseline reports the violation
 *               and the target's mutants do not run; under `ensures` the
 *               precondition is inert and the target scores normally.
 *
 * Plus the preload's line padding: a mutant that empties a multi-line
 * object before an `ensures` must not shift the line the violation names.
 */
import { afterAll, beforeAll, describe, expect, test } from "bun:test";
import { resolve } from "node:path";
import { runEngine } from "../engine/index.ts";
import { mutatedText } from "../engine/preload.ts";
import { preloadPath } from "../engine/runner.ts";
import type { ContractsMode, EngineConfig, EngineResult, MutantResult } from "../engine/types.ts";
import { buildDb, loadMutationReport } from "../ingest.ts";
import { report } from "../report.ts";
import { createFixtureProject } from "./fixture-project.ts";

const PRIMITIVES = resolve(import.meta.dir, "../../../verify/src/primitives/index.ts");
const IMPORT = `import { ensures, requires } from ${JSON.stringify(PRIMITIVES)};`;

const ACCOUNT = [
  IMPORT, // 1
  'export const state = { loggedIn: false, role: "" };', // 2
  "export function login(role: string): { success: boolean } {", // 3
  "  try {", // 4
  '    requires(state.loggedIn === false, "must be logged out");', // 5
  "    state.loggedIn = true;", // 6
  '    state.role = role || "member";', // 7
  '    ensures(state.role !== "", "role is set");', // 8
  "    return { success: true };", // 9
  "  } catch {", // 10
  "    return { success: false };", // 11
  "  }", // 12
  "}", // 13
].join("\n");
const ACCOUNT_ENSURES_LINE = 8;
const ACCOUNT_ROLE_LINE = 7;

const SESSION = [
  IMPORT, // 1
  "export const session = { open: false };", // 2
  "export function close(): void {", // 3
  '  requires(session.open === true, "must be open");', // 4
  "  session.open = false;", // 5
  "}", // 6
].join("\n");
const SESSION_REQUIRES_LINE = 4;

const project = createFixtureProject("polly-mutate-contracts-", {
  "src/account.ts": ACCOUNT,
  "src/session.ts": SESSION,
  "tests/account.test.ts": [
    'import { beforeEach, expect, test } from "bun:test";',
    'import { login, state } from "../src/account.ts";',
    'beforeEach(() => { state.loggedIn = false; state.role = ""; });',
    'test("login sets loggedIn", () => {',
    '  login("");',
    "  expect(state.loggedIn).toBe(true);",
    "});",
  ].join("\n"),
  "tests/session.test.ts": [
    'import { expect, test } from "bun:test";',
    'import { close, session } from "../src/session.ts";',
    'test("close from cold", () => {',
    "  close();",
    "  expect(session.open).toBe(false);",
    "});",
  ].join("\n"),
});
afterAll(() => project.remove());

const config = (contracts: ContractsMode, targets: string[]): EngineConfig => ({
  cwd: project.dir,
  targets: targets.map((t) => ({ file: project.path(t) })),
  testInclude: ["tests/**/*.test.ts"],
  testPreload: [],
  mode: "matrix",
  coverage: "dynamic",
  concurrency: 4,
  timeout: { factor: 2, extraMs: 3000 },
  runner: { kind: "bun-test" },
  excludeMutators: [],
  ignoreVerifyCallsites: true,
  contracts,
  scratchCwd: true,
  typecheck: false,
  cacheDir: null,
  reportPath: project.path(`reports/${contracts}.json`),
});

let off: EngineResult;
let all: EngineResult;
let ensuresOnly: EngineResult;

beforeAll(async () => {
  off = await runEngine(config("off", ["src/account.ts"]));
  all = await runEngine(config("all", ["src/account.ts", "src/session.ts"]));
  ensuresOnly = await runEngine(config("ensures", ["src/session.ts"]));
}, 180_000);

function results(r: EngineResult, file: string): MutantResult[] {
  return r.targets.find((t) => t.file.endsWith(file))?.results ?? [];
}
function roleMutant(r: EngineResult): MutantResult | undefined {
  return results(r, "account.ts").find(
    (x) =>
      x.mutant.mutatorName === "LogicalOperator" &&
      x.mutant.location.start.line === ACCOUNT_ROLE_LINE
  );
}

describe("contracts off", () => {
  test("the mutant only an ensures could catch survives", () => {
    expect(roleMutant(off)?.status).toBe("Survived");
    expect(off.contractViolations).toEqual([]);
  });

  test("the sites are inventoried all the same", () => {
    const account = off.targets.find((t) => t.file.endsWith("account.ts"));
    expect(account?.contracts).toEqual([
      {
        file: project.path("src/account.ts"),
        line: 5,
        primitive: "requires",
        message: "must be logged out",
        handler: { from: 3, to: 13 },
      },
      {
        file: project.path("src/account.ts"),
        line: ACCOUNT_ENSURES_LINE,
        primitive: "ensures",
        message: "role is set",
        handler: { from: 3, to: 13 },
      },
    ]);
  });
});

describe("contracts all", () => {
  test("the swallowed ensures kills the mutant through the afterEach drain, attributed and contract-only", () => {
    const m = roleMutant(all);
    expect(m?.status).toBe("Killed");
    expect(m?.killedBy).toEqual(["tests/account.test.ts#login sets loggedIn@4"]);
    expect(m?.killedByContract).toEqual([`src/account.ts:${ACCOUNT_ENSURES_LINE}`]);
    expect(m?.contractOnly).toBe(true);
  });

  test("a mutant the assertion catches is not contract-only", () => {
    const m = results(all, "account.ts").find(
      (x) => x.mutant.mutatorName === "BooleanLiteral" && x.mutant.location.start.line === 6
    );
    expect(m?.status).toBe("Killed");
    expect(m?.killedByContract).toBeUndefined();
    expect(m?.contractOnly).toBeUndefined();
  });

  test("a test that violates a requires stops its target and is named", () => {
    expect(all.contractViolations).toEqual([
      {
        target: project.path("src/session.ts"),
        test: "tests/session.test.ts#close from cold@3",
        contracts: [`src/session.ts:${SESSION_REQUIRES_LINE}`],
      },
    ]);
    const session = results(all, "session.ts").filter((r) => r.status !== "Ignored");
    expect(session.length).toBeGreaterThan(0);
    expect(session.every((r) => r.status === "RuntimeError")).toBe(true);
    expect(session[0]?.statusReason).toBe("1 test(s) violate contracts");
  });

  test("the report carries the contracts block and renders the CONTRACTS section", async () => {
    const written = await loadMutationReport(project.path("reports/all.json"));
    expect(written.contracts?.mode).toBe("all");
    expect(written.contracts?.runner).toBe("bun-test");
    expect(written.contracts?.sites.map((s) => s.id)).toEqual([
      "src/account.ts:5",
      `src/account.ts:${ACCOUNT_ENSURES_LINE}`,
      `src/session.ts:${SESSION_REQUIRES_LINE}`,
    ]);
    expect(written.contracts?.violations).toEqual([
      {
        target: "src/session.ts",
        test: "tests/session.test.ts#close from cold@3",
        contracts: [`src/session.ts:${SESSION_REQUIRES_LINE}`],
      },
    ]);
    const db = buildDb(written);
    try {
      const text = report(db);
      expect(text).toContain("CONTRACTS  (requires/ensures as kill oracles — mode all, 3 site(s))");
      expect(text).toContain(`    src/account.ts:${ACCOUNT_ROLE_LINE}  LogicalOperator`);
      expect(text).toContain(
        `    src/account.ts:${ACCOUNT_ENSURES_LINE}  ensures  2 kill(s)  “role is set”`
      );
      expect(text).toContain("TEST VIOLATES CONTRACT");
      // The account requires never fires: the test never drives login() logged in.
      expect(text).toContain("CONTRACTS WITHOUT TEETH");
      expect(text).toContain("    src/account.ts:5  requires  “must be logged out”");
    } finally {
      db.close();
    }
  });
});

describe("contracts ensures", () => {
  test("a false requires is inert, so the same test is a green baseline", () => {
    expect(ensuresOnly.contractViolations).toEqual([]);
    const session = results(ensuresOnly, "session.ts");
    expect(session.some((r) => r.status === "Killed")).toBe(true);
  });
});

describe("line padding", () => {
  test("mutatedText keeps the line count when a replacement drops lines", () => {
    const src = "a\n{\n  b,\n  c\n}\nd";
    const padded = mutatedText(src, { start: 2, end: 14, replacement: "{}" });
    expect(padded.split("\n").length).toBe(src.split("\n").length);
    expect(padded).toBe("a\n{}/*\n\n\n*/\nd");
    expect(mutatedText("a + b", { start: 2, end: 3, replacement: "-" })).toBe("a - b");
  });

  test("a mutant that empties a multi-line object before an ensures leaves its line unchanged", async () => {
    const site = project.path("src/site.ts");
    const text = [
      `import { ensures } from ${JSON.stringify(PRIMITIVES)};`, // 1
      "export function f(): void {", // 2
      "  const block = {", // 3
      "    a: 1,", // 4
      "    b: 2,", // 5
      "  };", // 6
      "  void block;", // 7
      '  try { ensures(false, "post"); } catch (e) { console.log((e as Error).message); }', // 8
      "}", // 9
      "f();", // 10
    ].join("\n");
    await Bun.write(site, text);
    const start = text.indexOf("{", text.indexOf("const block"));
    const end = text.indexOf("}", start) + 1;
    expect(text.slice(start, end).split("\n").length).toBe(4);
    const proc = Bun.spawn(["bun", "--preload", preloadPath(), site], {
      env: {
        ...process.env,
        POLLY_CONTRACTS: "all",
        POLLY_MUTATE_FILE: site,
        POLLY_MUTATE_SPAN: JSON.stringify({ start, end, replacement: "{}" }),
      },
      stdout: "pipe",
      stderr: "pipe",
    });
    const [stdout, stderr, code] = await Promise.all([
      new Response(proc.stdout).text(),
      new Response(proc.stderr).text(),
      proc.exited,
    ]);
    expect(code, stderr).toBe(0);
    expect(stdout.trim()).toBe(`[polly-contract ensures ${site}:8] post`);
  });
});
