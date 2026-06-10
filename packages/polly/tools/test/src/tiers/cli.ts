#!/usr/bin/env bun
/**
 * Consumer-facing tiered test runner — what `polly test --tier …` runs from a
 * consumer's own Polly project. It auto-discovers the project's tiers (see
 * discover.ts) and runs them through the shared engine, exactly as Polly's own
 * internal suite does.
 *
 * Usage (from a Polly project root):
 *   polly test --tier            # discovered unit + integration (fast loop)
 *   polly test --tier --all      # every discovered tier
 *   polly test --tier=browser    # one tier
 *   polly test --tier --list     # show what was discovered, run nothing
 *   polly test --tier --json     # write test-results/tiers.json
 *
 * (Bare `polly test` still delegates to `bun test`; the --tier-family flags
 *  switch into this runner.)
 */
import { mkdirSync } from "node:fs";
import { dirname } from "node:path";
import { parseTierArgs } from "./args";
import { discoverPlan } from "./discover";
import { runPlan } from "./engine";
import { formatPlan, formatSummary, toJSON } from "./reporter";

/** Tiers run when no tier is named (fast inner loop), if they were discovered. */
const DEFAULT_TIERS = ["unit", "integration"];

async function main(): Promise<void> {
  const args = parseTierArgs(process.argv.slice(2));
  const root = process.cwd();
  const plan = await discoverPlan(root);

  if (plan.tiers.length === 0) {
    console.log(
      "polly test: no tiers discovered.\n" +
        "  Looked for *.test.{ts,tsx}, *.browser.{ts,tsx}, and scripts/e2e-*.{ts,tsx}."
    );
    process.exit(0);
  }

  if (args.list) {
    console.log(formatPlan(plan));
    return;
  }

  const discovered = plan.tiers.map((t) => t.name);
  const known = new Set(discovered);
  let tiers: string[];
  if (args.tiers.length > 0) {
    const unknown = args.tiers.filter((t) => !known.has(t));
    if (unknown.length > 0) {
      console.log(`Unknown tier(s): ${unknown.join(", ")}`);
      console.log(`Discovered tiers: ${discovered.join(", ")}`);
      process.exit(2);
    }
    tiers = args.tiers;
  } else if (args.all || args.full) {
    tiers = discovered;
  } else {
    const fast = discovered.filter((t) => DEFAULT_TIERS.includes(t));
    tiers = fast.length > 0 ? fast : discovered;
  }

  console.log(
    `polly test — tiers: ${tiers.join(" → ")}${args.only.length ? `  only: ${args.only.join(", ")}` : ""}`
  );

  const report = await runPlan(plan, {
    tiers,
    only: args.only,
    bail: args.bail,
    strictNeeds: args.strictNeeds,
    cwd: root,
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
