/**
 * @fairfox/polly/test/e2e-cli — spawn the polly CLI from the working tree.
 *
 * The scripts invoke `cli/polly.ts` from this checkout, NOT a globally
 * installed `polly`, so an init/build/quality e2e exercises the code under
 * test rather than whatever happens to be on PATH. Output is captured (not
 * inherited) so a script can assert on stdout/stderr and exit code.
 */

import { resolve } from "node:path";

/** Absolute path to the polly package root (packages/polly). Scripts use
 *  this to override a scaffold's `@fairfox/polly` dependency at `file:` so
 *  the build resolves the working tree offline, not a published version. */
export const POLLY_PKG_DIR = resolve(import.meta.dir, "../../../..");

/** Absolute path to the polly CLI entry point in this checkout. */
const POLLY_BIN = resolve(POLLY_PKG_DIR, "cli/polly.ts");

export interface RunResult {
  exitCode: number;
  stdout: string;
  stderr: string;
}

export interface RunOptions {
  cwd: string;
  env?: Record<string, string>;
}

/** Spawn `bun <args>` in `cwd`, capturing stdout/stderr and the exit code. */
export async function runBun(args: string[], options: RunOptions): Promise<RunResult> {
  const proc = Bun.spawn(["bun", ...args], {
    cwd: options.cwd,
    stdout: "pipe",
    stderr: "pipe",
    env: { ...process.env, ...(options.env ?? {}) },
  });
  const [stdout, stderr, exitCode] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  return { exitCode, stdout, stderr };
}

/** Spawn the working-tree polly CLI: `bun cli/polly.ts <args>`. */
export function runCli(args: string[], options: RunOptions): Promise<RunResult> {
  return runBun([POLLY_BIN, ...args], options);
}
