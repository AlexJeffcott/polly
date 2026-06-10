#!/usr/bin/env bun
/**
 * Polly's internal tiered test runner.
 *
 * Drives the engine in tools/test/src/tiers over the plan in registry.ts.
 * Invoked directly (`bun scripts/test/cli.ts ...`), via package.json aliases,
 * and by `polly test --tier …` (which spawns this file in-repo).
 *
 * Usage:
 *   bun scripts/test/cli.ts                 # fast inner loop: unit + integration
 *   bun scripts/test/cli.ts --all           # everything realistic (no Docker)
 *   bun scripts/test/cli.ts --full          # + verify (Docker) + static gate
 *   bun scripts/test/cli.ts --tier=e2e-mesh # one tier
 *   bun scripts/test/cli.ts e2e-cli e2e-relay   # tiers positionally
 *   bun scripts/test/cli.ts --only=revocation   # filter cases across tiers
 *   bun scripts/test/cli.ts --list          # show the plan, run nothing
 *   bun scripts/test/cli.ts --all --json=test-results/tiers.json
 */
import { mkdirSync } from "node:fs";
import { dirname } from "node:path";
import {
  formatPlan,
  formatSummary,
  parseTierArgs,
  runPlan,
  type TierArgs,
  toJSON,
} from "../../tools/test/src/tiers";
import { ALL_TIERS, DEFAULT_TIERS, internalPlan, packageRoot, TIER_NAMES } from "./registry";

const KNOWN_TIERS = new Set<string>(TIER_NAMES);

function resolveTiers(args: TierArgs): string[] {
  if (args.tiers.length > 0) {
    const unknown = args.tiers.filter((t) => !KNOWN_TIERS.has(t));
    if (unknown.length > 0) {
      console.log(`Unknown tier(s): ${unknown.join(", ")}`);
      console.log(`Known tiers: ${TIER_NAMES.join(", ")}`);
      process.exit(2);
    }
    return args.tiers;
  }
  if (args.full) return [...TIER_NAMES];
  if (args.all) return ALL_TIERS;
  return DEFAULT_TIERS;
}

async function main(): Promise<void> {
  const args = parseTierArgs(process.argv.slice(2));
  const plan = internalPlan();

  if (args.list) {
    console.log(formatPlan(plan));
    return;
  }

  const tiers = resolveTiers(args);
  console.log(
    `polly test — tiers: ${tiers.join(" → ")}${args.only.length ? `  only: ${args.only.join(", ")}` : ""}`
  );

  const report = await runPlan(plan, {
    tiers,
    only: args.only,
    bail: args.bail,
    strictNeeds: args.strictNeeds,
    cwd: packageRoot,
    log: (m) => console.log(m),
  });

  console.log(formatSummary(report));

  if (args.json) {
    mkdirSync(dirname(args.json), { recursive: true });
    await Bun.write(args.json, toJSON(report));
    console.log(`\nwrote ${args.json}`);
  }

  process.exit(report.ok ? 0 : 1);
}

await main();
