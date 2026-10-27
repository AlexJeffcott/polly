#!/usr/bin/env bun
/**
 * E2e: `polly verify` names the handlers TLC never took.
 *
 * A handler whose `requires` guards never all hold at a reachable state is
 * never taken, and every `ensures` on it passes unchecked. examples/minimal,
 * examples/full-featured and examples/mesh-recovery-pair all passed that way:
 * green runs over handlers the model never executed.
 *
 * The run uses TLC `-coverage`: the effect conjunct of a handler is evaluated
 * only where every guard held, so a count of 0 on it means never taken.
 *
 * This harness runs the working-tree CLI on a copy of examples/todo-list (three
 * subsystems), then on the same copy with one guard that can never hold added
 * to SET_THEME:
 *
 *   | copy                 | flags      | expected                              |
 *   |----------------------|------------|---------------------------------------|
 *   | intact               | --strict   | exit 0, no handler reported           |
 *   | SET_THEME guard dead | (none)     | exit 0, HandleSetTheme reported       |
 *   | SET_THEME guard dead | --strict   | exit 1, the preferences subsystem fails |
 *
 * The copy sits beside the examples so its tsconfig `paths` resolve as the
 * original's do, and is removed afterwards.
 *
 * Needs: Docker and the `polly-tla:latest` image.
 */

export const capability = "verify.handler-coverage" as const;

import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { stripVTControlCharacters } from "node:util";
import { runCli } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const EXAMPLES_DIR = resolve(import.meta.dir, "../../../examples");
const TODO_LIST_DIR = join(EXAMPLES_DIR, "todo-list");

const SET_THEME = `bus.on("SET_THEME", (payload: { theme: "light" | "dark" | "system" }) => {\n`;
const DEAD_GUARD = `    requires(theme.value === "midnight", "e2e: a guard that never holds");\n`;

function copyTodoList(): string {
  const dir = mkdtempSync(join(EXAMPLES_DIR, ".e2e-handler-coverage-"));
  for (const entry of ["src", "specs", "tsconfig.json", "package.json"]) {
    cpSync(join(TODO_LIST_DIR, entry), join(dir, entry), { recursive: true });
  }
  rmSync(join(dir, "specs", "tla", "generated"), { recursive: true, force: true });
  symlinkSync(join(TODO_LIST_DIR, "node_modules"), join(dir, "node_modules"));
  return dir;
}

async function verify(cwd: string, args: string[]): Promise<{ exitCode: number; output: string }> {
  const result = await runCli(["verify", ...args], { cwd });
  const output = stripVTControlCharacters(`${result.stdout}\n${result.stderr}`);
  return { exitCode: result.exitCode, output };
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const dir = copyTodoList();
  try {
    // 1. Intact: every handler in the model runs, so --strict passes.
    ctx.log("[e2e] polly verify --strict (todo-list copy, intact)");
    const intact = await verify(dir, ["--strict"]);
    assert(intact.exitCode === 0, `intact copy failed under --strict:\n${intact.output}`);
    assert(
      !/never taken/.test(intact.output),
      `intact copy reported a handler never taken:\n${intact.output}`
    );

    // 2. One guard that never holds.
    const handlersPath = join(dir, "src", "background", "handlers.ts");
    const handlers = readFileSync(handlersPath, "utf-8");
    assert(handlers.includes(SET_THEME), "SET_THEME handler not found — the probe is a no-op");
    writeFileSync(handlersPath, handlers.replace(SET_THEME, SET_THEME + DEAD_GUARD));

    ctx.log("[e2e] polly verify (SET_THEME guard never holds)");
    const warned = await verify(dir, []);
    assert(warned.exitCode === 0, `without --strict the run must still pass:\n${warned.output}`);
    assert(
      /preferences: never taken — HandleSetTheme/.test(warned.output),
      `HandleSetTheme was not reported as never taken. The run passed over a ` +
        `handler the model never executed.\n${warned.output}`
    );

    ctx.log("[e2e] polly verify --strict (SET_THEME guard never holds)");
    const failed = await verify(dir, ["--strict"]);
    assert(failed.exitCode !== 0, `--strict passed over a handler never taken:\n${failed.output}`);
    assert(
      /Failed: preferences/.test(failed.output),
      `--strict did not fail the preferences subsystem:\n${failed.output}`
    );

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
