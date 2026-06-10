#!/usr/bin/env bun
/**
 * E2e: `polly quality` CLI, from cold state.
 *
 * `polly quality` is a documented CLI surface a consumer can run, but
 * nothing drove it end to end from outside. (It is polly's own conformance
 * suite — import boundaries, no-marketing, SAST — not a scaffold linter, so
 * running the whole suite green against an arbitrary project is not a
 * meaningful assertion; this script tests the CLI's plumbing instead.)
 *
 * Against a throwaway fixture, using the working-tree CLI:
 *
 *   1. `polly quality list` exits 0 and lists the available checks.
 *   2. A clean fixture passes `polly quality run polly:no-require` (exit 0).
 *   3. The same check on a fixture containing a `require(...)` call exits
 *      non-zero and names the offending file — proof the check actually
 *      inspects the target rather than rubber-stamping it.
 *
 * `polly:no-require` is chosen because it is deterministic and needs no
 * external tools (unlike the secrets/SAST checks, which shell out to
 * gitleaks / semgrep).
 */

export const capability = "cli.quality" as const;

import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { runCli, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir("polly-e2e-quality-");
  const srcDir = join(temp.dir, "src");
  mkdirSync(srcDir, { recursive: true });

  try {
    writeFileSync(
      join(srcDir, "clean.ts"),
      "export const greet = (name: string): string => name.trim();\n"
    );

    ctx.log("[e2e] polly quality list");
    const list = await runCli(["quality", "list"], { cwd: temp.dir });
    assert(list.exitCode === 0, `quality list exited ${list.exitCode}\n${list.stderr}`);
    assert(/no-require/.test(list.stdout), "quality list should mention polly:no-require");

    ctx.log("[e2e] polly quality run polly:no-require (clean fixture → pass)");
    const clean = await runCli(["quality", "run", "polly:no-require", "--root", temp.dir], {
      cwd: temp.dir,
    });
    assert(
      clean.exitCode === 0,
      `clean fixture should pass; exited ${clean.exitCode}\n${clean.stdout}\n${clean.stderr}`
    );

    // Introduce a violation and re-run the same check.
    writeFileSync(
      join(srcDir, "dirty.ts"),
      'const fs = require("node:fs");\nexport const handle = fs;\n'
    );
    ctx.log("[e2e] polly quality run polly:no-require (require() fixture → fail)");
    const dirty = await runCli(["quality", "run", "polly:no-require", "--root", temp.dir], {
      cwd: temp.dir,
    });
    assert(dirty.exitCode !== 0, "a fixture containing require(...) must fail polly:no-require");
    const dirtyOutput = `${dirty.stdout}\n${dirty.stderr}`;
    assert(
      /dirty\.ts/.test(dirtyOutput),
      `the failure should name the offending file; got:\n${dirtyOutput}`
    );

    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    temp.cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
