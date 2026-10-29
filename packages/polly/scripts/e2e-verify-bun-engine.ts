#!/usr/bin/env bun
/**
 * E2e: `polly verify --engine bun` runs the safety pass on polly's own checker,
 * without Docker, and fails where TLC fails.
 *
 * The checker (tools/verify/src/checker) compiles the generated `.tla` and
 * gives TLC's generated / distinct / depth counts exactly on every example
 * spec set (scripts/e2e-verify-bun-parity.ts, which needs Docker). This
 * harness is the user's side: the working-tree CLI, on copies of two examples
 * with no generated specs, so the run starts from the state a fresh checkout
 * has.
 *
 *   | copy                         | flags                  | expected                                   |
 *   |------------------------------|------------------------|--------------------------------------------|
 *   | minimal                      | --engine bun           | exit 0, no Docker, PROPERTIES listed       |
 *   | minimal                      | --engine bun --strict  | exit 1: PROPERTIES not checked             |
 *   | minimal + capability ACTIVATE | --engine bun          | exit 1, the invariant named, a trace       |
 *   |   breaks (falsification)     |                        |                                            |
 *   | todo-list (3 subsystems)     | --engine bun           | exit 0, no Docker                          |
 *   | todo-list, SET_THEME guard   | --engine bun           | exit 0, HandleSetTheme never taken         |
 *   |   that never holds           |                        |                                            |
 *
 * The capability row is the falsification gate: a checker that passes every
 * spec passes every other row too. The SET_THEME row checks the checker's own
 * handler counter, which replaces TLC `-coverage` on this engine.
 *
 * Copies sit beside the examples so their tsconfig `paths` resolve as the
 * originals' do, and are removed afterwards. Needs no Docker.
 */

export const capability = "verify.bun-engine" as const;

import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { stripVTControlCharacters } from "node:util";
import { runCli } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const EXAMPLES_DIR = resolve(import.meta.dir, "../../../examples");

const SET_THEME = `bus.on("SET_THEME", (payload: { theme: "light" | "dark" | "system" }) => {\n`;
const DEAD_GUARD = `    requires(theme.value === "midnight", "e2e: a guard that never holds");\n`;

const CAPABILITY = `  capabilities: [
    {
      name: "E2eNeverActive",
      enabledBy: "user.value.active === true",
      requires: "user.value.active === false",
      message: "e2e: a capability that ACTIVATE breaks",
    },
  ],

`;

/** A copy of an example's tracked files, as a fresh checkout has them. */
function copyExample(name: string): string {
  const source = join(EXAMPLES_DIR, name);
  const dir = mkdtempSync(join(EXAMPLES_DIR, `.e2e-bun-engine-${name}-`));
  const tracked = Bun.spawnSync(["git", "ls-files", "-z", "."], { cwd: source, stdout: "pipe" });
  const files = tracked.stdout.toString().split("\0").filter(Boolean);
  if (tracked.exitCode !== 0 || files.length === 0) throw new Error(`${name}: no tracked files`);
  for (const file of files) cpSync(join(source, file), join(dir, file), { recursive: true });
  symlinkSync(join(source, "node_modules"), join(dir, "node_modules"));
  return dir;
}

async function verify(cwd: string, args: string[]): Promise<{ exitCode: number; output: string }> {
  const result = await runCli(["verify", "--engine", "bun", ...args], { cwd });
  const output = stripVTControlCharacters(`${result.stdout}\n${result.stderr}`);
  return { exitCode: result.exitCode, output };
}

function assertNoDocker(output: string, label: string): void {
  assert(
    !/Checking Docker|Running TLC/.test(output),
    `${label}: the Bun engine run started Docker or TLC:\n${output}`
  );
  assert(
    /Running the Bun model checker|Verifying subsystem/.test(output),
    `${label}: the run did not reach the model checker:\n${output}`
  );
}

async function checkMinimal(ctx: TierContext): Promise<void> {
  const dir = copyExample("minimal");
  try {
    ctx.log("[e2e] polly verify --engine bun (minimal copy)");
    const passed = await verify(dir, []);
    assert(passed.exitCode === 0, `minimal failed on the Bun engine:\n${passed.output}`);
    assertNoDocker(passed.output, "minimal");
    assert(/Verification passed/.test(passed.output), `no pass reported:\n${passed.output}`);
    const distinct = /Distinct states: (\d+)/.exec(passed.output)?.[1];
    assert(
      distinct !== undefined && Number(distinct) > 1,
      `no distinct-state count above the initial state:\n${passed.output}`
    );
    assert(
      /temporal properties not checked[\s\S]*EnsuresAfter_HandleActivate/.test(passed.output),
      `the PROPERTIES the Bun engine skipped were not listed:\n${passed.output}`
    );
    ctx.log(`[e2e] minimal passed, ${distinct} distinct states, PROPERTIES listed`);

    ctx.log("[e2e] polly verify --engine bun --strict (minimal copy)");
    const strict = await verify(dir, ["--strict"]);
    assert(strict.exitCode !== 0, `--strict passed with PROPERTIES unchecked:\n${strict.output}`);
    assert(
      /--strict: 2 PROPERTIES not checked by the Bun engine/.test(strict.output),
      `--strict did not name the unchecked PROPERTIES as the reason:\n${strict.output}`
    );

    // Falsification: a capability invariant that ACTIVATE breaks.
    const configPath = join(dir, "specs", "verification.config.ts");
    const config = readFileSync(configPath, "utf-8");
    assert(config.includes("  messages: {"), "no messages block in the config — probe is a no-op");
    writeFileSync(configPath, config.replace("  messages: {", `${CAPABILITY}  messages: {`));

    ctx.log("[e2e] polly verify --engine bun (minimal copy, capability ACTIVATE breaks)");
    const failed = await verify(dir, []);
    assert(failed.exitCode !== 0, `a broken invariant passed on the Bun engine:\n${failed.output}`);
    assert(
      /Invariant violated: Capability_E2eNeverActive/.test(failed.output),
      `the broken invariant was not named:\n${failed.output}`
    );
    // The report shows the first 20 trace lines; the log has all of them.
    const log = readFileSync(join(dir, "specs", "tla", "generated", "tlc-output.log"), "utf-8");
    assert(
      /State 1: <Initial predicate>/.test(log) && /user_active \|-> TRUE/.test(log),
      `no trace from the initial state to user_active = TRUE in tlc-output.log:\n${log}`
    );
    assertNoDocker(failed.output, "minimal, broken capability");
    ctx.log("[e2e] the broken capability failed the run with a trace");
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

async function checkTodoList(ctx: TierContext): Promise<void> {
  const dir = copyExample("todo-list");
  try {
    ctx.log("[e2e] polly verify --engine bun (todo-list copy, 3 subsystems)");
    const passed = await verify(dir, []);
    assert(passed.exitCode === 0, `todo-list failed on the Bun engine:\n${passed.output}`);
    assertNoDocker(passed.output, "todo-list");
    assert(/Compositional result: ✓ PASS/.test(passed.output), `no PASS:\n${passed.output}`);
    assert(
      !/never taken/.test(passed.output),
      `intact copy: a handler never taken:\n${passed.output}`
    );

    const handlersPath = join(dir, "src", "background", "handlers.ts");
    const handlers = readFileSync(handlersPath, "utf-8");
    assert(handlers.includes(SET_THEME), "SET_THEME handler not found — the probe is a no-op");
    writeFileSync(handlersPath, handlers.replace(SET_THEME, SET_THEME + DEAD_GUARD));

    ctx.log("[e2e] polly verify --engine bun (todo-list copy, SET_THEME guard never holds)");
    const dead = await verify(dir, []);
    assert(dead.exitCode === 0, `without --strict the run must still pass:\n${dead.output}`);
    assert(
      /preferences: never taken — HandleSetTheme/.test(dead.output),
      `the Bun engine's handler counter did not report HandleSetTheme:\n${dead.output}`
    );
    ctx.log("[e2e] the Bun engine reported HandleSetTheme as never taken");
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    await checkMinimal(ctx);
    await checkTodoList(ctx);
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
