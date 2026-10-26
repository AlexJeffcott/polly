#!/usr/bin/env bun
/**
 * E2e: `scripts/vendor-polly.sh --check` produces a slice that type-checks
 * and builds, and the script exits 0 only when it does.
 *
 * Nothing ran the script, so it drifted while polly grew: by 0.97.1 its
 * `--check` reported 8 type errors (two mesh files and tools/mutate left in
 * the slice) and still exited 0, and three of its import redirects pointed
 * at imports that no longer existed. This script vendors polly into an empty
 * directory, from cold, and requires:
 *
 *   1. exit 0 from `vendor-polly.sh <polly> <target> --check` (bun install,
 *      bun check and build:lib in the slice);
 *   2. no `⚠` line in its output (a stale redirect or a skipped file warns);
 *   3. no `@automerge/*` import left in the slice's src/, tools/ or cli/.
 *
 * Run in one command: `bun scripts/e2e-vendor-polly.ts`.
 */

export const capability = "cli.vendor-polly" as const;

import { readdirSync, readFileSync, statSync } from "node:fs";
import { join } from "node:path";
import { POLLY_PKG_DIR, withTempDir } from "../tools/test/src/e2e-cli";
import { assert, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";
import { describe, runAlarmed } from "./e2e-analysis-cold-install.ts";

const VENDOR_ALARM_S = 300;
const AUTOMERGE_IMPORT = /from\s+["']@automerge\/|import\(\s*["']@automerge\//;

/** Every .ts/.tsx file under `dir`. */
function sourceFiles(dir: string): string[] {
  const out: string[] = [];
  for (const name of readdirSync(dir)) {
    const path = join(dir, name);
    if (name === "node_modules" || name === "dist") continue;
    if (statSync(path).isDirectory()) out.push(...sourceFiles(path));
    else if (/\.tsx?$/.test(name)) out.push(path);
  }
  return out;
}

export async function run(ctx: TierContext): Promise<TierResult> {
  const temp = withTempDir("polly-e2e-vendor-");
  try {
    const target = join(temp.dir, "slice");
    ctx.log(`[e2e] vendor-polly.sh ${POLLY_PKG_DIR} ${target} --check`);
    const r = await runAlarmed(
      ["bash", join(POLLY_PKG_DIR, "scripts/vendor-polly.sh"), POLLY_PKG_DIR, target, "--check"],
      temp.dir,
      VENDOR_ALARM_S
    );
    assert(r.exitCode === 0, `vendor-polly.sh --check: ${describe(r)}`);
    const warnings = `${r.stdout}\n${r.stderr}`.split("\n").filter((l) => l.includes("⚠"));
    assert(warnings.length === 0, `vendor-polly.sh warned:\n${warnings.join("\n")}`);

    const automerge = ["src", "tools", "cli"]
      .flatMap((tree) => sourceFiles(join(target, tree)))
      .filter((file) => AUTOMERGE_IMPORT.test(readFileSync(file, "utf8")));
    assert(
      automerge.length === 0,
      `@automerge imports left in the slice:\n${automerge.join("\n")}`
    );

    return { pass: true, message: "slice type-checks and builds" };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  } finally {
    temp.cleanup();
  }
}

if (import.meta.main) await selfRun(capability, run);
