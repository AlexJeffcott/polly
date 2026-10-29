#!/usr/bin/env bun
/**
 * The Bun safety checker on one spec directory, outside `polly verify`: for
 * the parity gate (scripts/e2e-verify-bun-parity.ts) and the bench scripts
 * (scripts/spikes/bun-checker/), which compare its counts and time with
 * TLC's.
 *
 * Usage: bun cli.ts --spec DIR [--module NAME]
 * Prints: "N states generated, M distinct states found, depth D" (TLC's counts)
 * Exit:   0 no error; 12 invariant violated or deadlock (TLC's code);
 *         3 the spec uses TLA+ this checker does not support.
 */

import { readdirSync } from "node:fs";
import { checkSpec } from "./check";

function main(): number {
  const args = process.argv.slice(2);
  const opt = (name: string): string | undefined => {
    const i = args.indexOf(name);
    return i >= 0 ? args[i + 1] : undefined;
  };
  const specDir = opt("--spec") ?? ".";
  const cfgs = readdirSync(specDir).filter((f) => f.endsWith(".cfg") && !f.startsWith("Witness_"));
  const [only] = cfgs;
  const moduleName =
    opt("--module") ?? (cfgs.length === 1 ? only?.replace(/\.cfg$/, "") : undefined);
  if (!moduleName) {
    console.log(
      `unsupported: ${specDir}: name the module with --module (${cfgs.length} .cfg files)`
    );
    return 3;
  }

  const result = checkSpec({ specDir, moduleName });
  if (result.kind === "unsupported") {
    console.log(`unsupported: ${result.reason}`);
    return 3;
  }
  if (result.properties.length > 0) {
    process.stderr.write(
      `note: PROPERTIES not checked (safety only): ${result.properties.join(", ")}\n`
    );
  }
  if (result.kind === "violation") {
    console.log(
      result.what === "deadlock"
        ? "Error: Deadlock reached."
        : `Error: Invariant ${result.name} is violated.`
    );
    for (const line of result.trace) console.log(`  ${line}`);
  }
  const c = result.counts;
  console.log(
    `${c.generated} states generated, ${c.distinct} distinct states found, depth ${c.depth}`
  );
  console.log(
    `wall ${result.seconds.toFixed(3)} s; rss ${(process.memoryUsage().rss / 2 ** 30).toFixed(2)} GiB`
  );
  return result.kind === "violation" ? 12 : 0;
}

process.exit(main());
