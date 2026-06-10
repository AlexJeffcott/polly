#!/usr/bin/env bun
/**
 * e2e: the polly#143 Stryker ignorer for verify primitives.
 *
 * Runs real Stryker against tools/verify/test-projects/stryker-verify — a
 * fixture whose `transition()` puts string literals and comparison operators
 * inside `requires(...)` / `ensures(...)` (the survivors from the issue) right
 * next to a real `label === "go" ? ... : ...` ternary that must still be
 * mutated. Stryker is driven through its actual plugin loader, ignorer
 * activation, dependency injection, and Babel instrumenter — not a hand-wired
 * stand-in.
 *
 * Two runs, the second a falsification gate:
 *
 *   1. excludeVerifyCallsites: true  → every mutant inside requires/ensures is
 *      reported "Ignored" with a polly#143 reason, while the real ternary
 *      mutants are not. Proves the ignorer suppresses the right callsites
 *      without swallowing production logic.
 *
 *   2. excludeVerifyCallsites: false → those same callsite mutants come back as
 *      "Survived" and zero carry the polly#143 reason. Proves the plugin is
 *      load-bearing: with it off, the survivors return. If a future change made
 *      the ignorer a silent no-op, this run fails loudly instead of going green.
 *
 * The plugin is loaded by absolute path to the built dist. In this monorepo's
 * bun-isolated install layout Stryker cannot resolve the bare
 * "@fairfox/polly/stryker" specifier from inside its own package; a real
 * downstream consumer (flat node_modules) resolves it normally — that path is
 * covered by the unit tests and the documented stryker.conf.json.
 *
 * Usage:  bun scripts/e2e-stryker-verify.ts
 * Needs:  `bun run build:lib` first (reads dist/.../stryker/index.js).
 */

import { existsSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fail, selfRun, type TierContext, type TierResult } from "../tools/test/src/e2e-shared";

export const capability = "stryker.verify" as const;

const FIXTURE_DIR = resolve(import.meta.dir, "../tools/verify/test-projects/stryker-verify");
const PLUGIN_PATH = resolve(import.meta.dir, "../dist/tools/verify/src/stryker/index.js");
const REPORT_PATH = join(FIXTURE_DIR, "reports", "mutation", "mutation.json");

interface Mutant {
  mutatorName: string;
  status: string;
  statusReason?: string;
  location: { start: { line: number } };
}

/** Run Stryker on the fixture with the ignorer enabled or disabled. */
async function runStryker(excludeVerifyCallsites: boolean): Promise<Mutant[]> {
  const configPath = join(FIXTURE_DIR, `.stryker-e2e.${excludeVerifyCallsites}.json`);
  writeFileSync(
    configPath,
    JSON.stringify({
      testRunner: "command",
      commandRunner: { command: "exit 0" },
      coverageAnalysis: "off",
      checkers: [],
      reporters: ["json"],
      plugins: [PLUGIN_PATH],
      ignorers: ["polly-verify"],
      polly: { excludeVerifyCallsites },
      mutate: ["src/machine.js"],
      concurrency: 1,
      timeoutMS: 30000,
    })
  );
  rmSync(REPORT_PATH, { force: true });

  const proc = Bun.spawn(["bunx", "stryker", "run", configPath], {
    cwd: FIXTURE_DIR,
    stdout: "pipe",
    stderr: "pipe",
  });
  const exitCode = await proc.exited;
  if (exitCode !== 0) {
    const err = await new Response(proc.stderr).text();
    fail(`Stryker exited ${exitCode} (excludeVerifyCallsites=${excludeVerifyCallsites}):\n${err}`);
  }
  rmSync(configPath, { force: true });

  if (!existsSync(REPORT_PATH)) {
    fail(`Stryker produced no report at ${REPORT_PATH}`);
  }
  const report = await Bun.file(REPORT_PATH).json();
  return Object.values(report.files as Record<string, { mutants: Mutant[] }>).flatMap(
    (f) => f.mutants
  );
}

function countWhere(mutants: Mutant[], predicate: (m: Mutant) => boolean): number {
  return mutants.filter(predicate).length;
}

const isVerifyIgnored = (m: Mutant) =>
  m.status === "Ignored" && (m.statusReason ?? "").includes("polly#143");

// The real ternary lives on its own line; lock onto it so we can prove it is
// never ignored regardless of the flag.
const TERNARY_LINE = 15;
const onTernaryLine = (m: Mutant) => m.location.start.line === TERNARY_LINE;

export async function run(ctx: TierContext): Promise<TierResult> {
  try {
    if (!existsSync(PLUGIN_PATH)) {
      fail(`Built plugin not found at ${PLUGIN_PATH}. Run \`bun run build:lib\` first.`);
    }
    mkdirSync(dirname(REPORT_PATH), { recursive: true });

    ctx.log("▶ Run 1 — ignorer enabled (excludeVerifyCallsites: true)");
    const enabled = await runStryker(true);
    const ignored = countWhere(enabled, isVerifyIgnored);
    const ternaryMutantsEnabled = enabled.filter(onTernaryLine);
    const ternaryIgnored = countWhere(ternaryMutantsEnabled, isVerifyIgnored);

    ctx.log(`  ${enabled.length} mutants, ${ignored} ignored inside verify callsites`);
    if (ignored === 0) {
      fail(
        "Enabled run ignored nothing — the ignorer did not suppress any verify-callsite mutants."
      );
    }
    if (ternaryMutantsEnabled.length === 0) {
      fail(`No mutants generated on the real ternary (line ${TERNARY_LINE}); fixture drifted.`);
    }
    if (ternaryIgnored !== 0) {
      fail(
        `${ternaryIgnored} real-logic mutant(s) on line ${TERNARY_LINE} were ignored — the ignorer is too broad.`
      );
    }
    ctx.log(
      `  ✓ ${ignored} verify-callsite mutants ignored; ${ternaryMutantsEnabled.length} real-logic mutants left mutable`
    );

    ctx.log("\n▶ Run 2 — falsification gate (excludeVerifyCallsites: false)");
    const disabled = await runStryker(false);
    const stillIgnored = countWhere(disabled, isVerifyIgnored);
    ctx.log(`  ${disabled.length} mutants, ${stillIgnored} ignored by polly#143`);
    if (stillIgnored !== 0) {
      fail(
        `Falsification failed: ${stillIgnored} mutant(s) still ignored with the flag off. The ignorer is not actually load-bearing.`
      );
    }
    if (disabled.length !== enabled.length) {
      fail(
        `Mutant count changed between runs (${enabled.length} → ${disabled.length}); the flag should only change status, not generation.`
      );
    }
    ctx.log("  ✓ with the flag off, the suppressed survivors return — the plugin is load-bearing");

    ctx.log("\n✅ polly#143 Stryker ignorer verified end-to-end.\n");
    return { pass: true };
  } catch (err) {
    return { pass: false, message: err instanceof Error ? err.message : String(err) };
  }
}

if (import.meta.main) await selfRun(capability, run);
