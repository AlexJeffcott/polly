#!/usr/bin/env bun
/**
 * Type-filter parity probe: runs only the mutate engine's type filter over
 * the targets of a `polly.mutate.ts`, with no test runs, and writes every
 * verdict as JSON. Two runs (before and after a TypeScript upgrade) diff to
 * an exact answer on whether the filter's behaviour moved.
 *
 *   bun scripts/mutate-typecheck-parity.ts [--config ../../polly.mutate.ts] [--out verdicts.json]
 *
 * Prints mutant count, checked count, invalid count and wall time.
 */
import { dirname, resolve } from "node:path";
import { generateMutants } from "../tools/mutate/src/engine/generate.ts";
import { typecheckMutants } from "../tools/mutate/src/engine/typecheck.ts";

function flag(name: string, fallback: string): string {
  const i = process.argv.indexOf(name);
  const value = i >= 0 ? process.argv[i + 1] : undefined;
  return value ?? fallback;
}

const configPath = resolve(flag("--config", resolve(import.meta.dir, "../../../polly.mutate.ts")));
const out = flag("--out", "");
const cwd = dirname(configPath);
const config: { default: { targets: string[] } } = await import(configPath);

const targets = [];
let total = 0;
for (const rel of config.default.targets) {
  const file = resolve(cwd, rel);
  const src = await Bun.file(file).text();
  const mutants = generateMutants(file, src, { idPrefix: `${rel}:` }).mutants.filter(
    (m) => !m.ignoredReason
  );
  total += mutants.length;
  targets.push({ file, mutants });
}

const outcome = await typecheckMutants(targets, { cwd, log: (l) => console.log(l) });
if (!outcome) {
  console.log("type filter unavailable");
  process.exit(1);
}
console.log(
  `targets ${targets.length}  mutants ${total}  checked ${outcome.checked}  ` +
    `invalid ${outcome.invalid.size}  skipped ${outcome.skipped.length}  wall ${outcome.wallMs} ms`
);
if (out) {
  const verdicts = [...outcome.invalid].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
  await Bun.write(
    out,
    JSON.stringify({ total, checked: outcome.checked, skipped: outcome.skipped, verdicts }, null, 1)
  );
}
