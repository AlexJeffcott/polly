#!/usr/bin/env bun
/**
 * e2e: contracts as a kill oracle on a real consumer, examples/todo-list,
 * through the BDD command runner (`polly mutate run` → `bun run bdd` per
 * mutant). The handlers carry `requires`/`ensures` from
 * "@fairfox/polly/verify"; the scenarios drive the real factory bus.
 *
 * Two runs of the built CLI, no cache: `--contracts off` and `--contracts
 * all`. The kill counts are logged with their delta. There is no threshold:
 * the delta is the measurement, and a `TEST VIOLATES CONTRACT` stop under
 * `all` is logged as the result, since that finding is the deliverable.
 *
 * Usage:  bun scripts/e2e-mutate-contracts.ts
 * Needs:  `bun run build:lib` first (the example's `polly` is dist/cli/polly.js).
 */

import { existsSync } from "node:fs";
import { resolve } from "node:path";
import { POLLY_PKG_DIR, runBun } from "../tools/test/src/e2e-cli";
import {
  assert,
  fail,
  selfRun,
  type TierContext,
  type TierResult,
} from "../tools/test/src/e2e-shared";

export const capability = "mutate.contracts" as const;

const BUILT_CLI = resolve(POLLY_PKG_DIR, "dist/cli/polly.js");
const EXAMPLE = resolve(POLLY_PKG_DIR, "../../examples/todo-list");

interface Counts {
  killed: number;
  survived: number;
  total: number;
}

/** The per-target summary row `polly mutate run` prints. */
function counts(out: string): Counts {
  const row = out.match(/^src\/background\/handlers\.ts \| \d+ \| (\d+) \| (\d+) \| /m);
  if (!row?.[1] || !row[2]) fail(`no summary row for handlers.ts in:\n${out}`);
  const total = out.match(/^(\d+) mutants in /m);
  return { killed: Number(row[1]), survived: Number(row[2]), total: Number(total?.[1] ?? 0) };
}

async function mutate(mode: "off" | "all"): Promise<{ exitCode: number; out: string }> {
  const r = await runBun(
    [BUILT_CLI, "mutate", "run", "--no-report", "--no-cache", "--contracts", mode],
    { cwd: EXAMPLE }
  );
  return { exitCode: r.exitCode, out: `${r.stdout}\n${r.stderr}` };
}

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    if (!existsSync(BUILT_CLI))
      fail(`Built CLI not found at ${BUILT_CLI}. Run \`bun run build:lib\` first.`);
    assert(existsSync(resolve(EXAMPLE, "polly.mutate.ts")), `${EXAMPLE} has no polly.mutate.ts`);

    ctx.log("[e2e] todo-list: polly mutate run --contracts off");
    const off = await mutate("off");
    assert(off.exitCode === 0, `--contracts off exited ${off.exitCode}:\n${off.out}`);
    const before = counts(off.out);

    ctx.log("[e2e] todo-list: polly mutate run --contracts all");
    const all = await mutate("all");
    if (all.out.includes("TEST VIOLATES CONTRACT")) {
      const block = all.out.slice(all.out.indexOf("TEST VIOLATES CONTRACT"));
      ctx.log(`  ✓ finding: a scenario violates a contract on the unmutated handlers\n${block}`);
      return { pass: true };
    }
    assert(all.exitCode === 0, `--contracts all exited ${all.exitCode}:\n${all.out}`);
    const after = counts(all.out);
    assert(after.total === before.total, `mutant count moved: ${before.total} → ${after.total}`);
    assert(
      after.killed >= before.killed,
      `contracts on killed fewer mutants (${after.killed}) than off (${before.killed})`
    );
    ctx.log(
      `  ✓ handlers.ts: killed off=${before.killed} all=${after.killed} (delta +${after.killed - before.killed} of ${after.total} mutants; survived ${before.survived} → ${after.survived})`
    );
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
