#!/usr/bin/env bun
/**
 * E2e: `polly verify` names a config message name that matches no message type.
 *
 * A name in `messages.include`, `subsystems.*.handlers`, `perMessageBounds` or
 * `tier2` that matches no type filters, bounds or orders nothing. Before this
 * check the run said nothing: examples/full-featured listed `SETTINGS_GET`
 * under `messages.include` for the `GET_SETTINGS` handler, so that handler was
 * out of the model and every run passed.
 *
 * This harness runs the working-tree CLI on a copy of examples/todo-list with
 * one unknown name, `THEME_SET`, added to `subsystems.preferences.handlers`:
 *
 *   | flags    | expected                                                |
 *   |----------|---------------------------------------------------------|
 *   | (none)   | exit 0, the name reported, TLC still runs               |
 *   | --strict | exit 1, the name reported, before TLC starts            |
 *
 * The intact todo-list passes `--strict` in verify.handler-coverage, so the
 * failure here comes from the added name only.
 *
 * Needs: Docker and the `polly-tla:latest` image (the run without --strict).
 */

export const capability = "verify.unknown-message-names" as const;

import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { stripVTControlCharacters } from "node:util";
import { runCli } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

const EXAMPLES_DIR = resolve(import.meta.dir, "../../../examples");
const TODO_LIST_DIR = join(EXAMPLES_DIR, "todo-list");

const PREFERENCES_HANDLERS = `handlers: ["SET_THEME"],`;
const WITH_UNKNOWN = `handlers: ["SET_THEME", "THEME_SET"],`;
const REPORTED = /subsystems\.preferences\.handlers: THEME_SET/;
// Printed once per subsystem TLC checks.
const TLC_RAN = /Verifying subsystem/;

function copyTodoList(): string {
  const dir = mkdtempSync(join(EXAMPLES_DIR, ".e2e-unknown-message-names-"));
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
    const configPath = join(dir, "specs", "verification.config.ts");
    const config = readFileSync(configPath, "utf-8");
    assert(
      config.includes(PREFERENCES_HANDLERS),
      "preferences handlers not found — the probe is a no-op"
    );
    writeFileSync(configPath, config.replace(PREFERENCES_HANDLERS, WITH_UNKNOWN));

    ctx.log("[e2e] polly verify --strict (unknown name THEME_SET)");
    const strict = await verify(dir, ["--strict"]);
    assert(strict.exitCode !== 0, `--strict passed over an unknown name:\n${strict.output}`);
    assert(REPORTED.test(strict.output), `THEME_SET was not reported:\n${strict.output}`);
    assert(!TLC_RAN.test(strict.output), `--strict ran TLC before failing:\n${strict.output}`);

    ctx.log("[e2e] polly verify (unknown name THEME_SET)");
    const warned = await verify(dir, []);
    assert(warned.exitCode === 0, `without --strict the run must still pass:\n${warned.output}`);
    assert(REPORTED.test(warned.output), `THEME_SET was not reported:\n${warned.output}`);
    assert(TLC_RAN.test(warned.output), `the run stopped before TLC:\n${warned.output}`);

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

if (import.meta.main) await selfRun(capability, run);
