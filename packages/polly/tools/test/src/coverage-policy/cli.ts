#!/usr/bin/env bun

/**
 * @fairfox/polly/test/coverage — consumer-facing `polly coverage`.
 *
 * Zero-config: run it in any Polly project and it reports per-file coverage,
 * orphan source files, and (if a Stryker config is present) dead mutate/test
 * globs. Add a `coverage.config.ts` with a `defaultThreshold` to turn the
 * report into an enforced gate, and `exempt` entries to record which
 * higher-tier test covers a unit-thin file.
 *
 * Usage:
 *   polly coverage                 # report (zero-config) or enforce (with config)
 *   polly coverage --strict-orphans  # fail on source no unit test imports
 *   polly coverage --orphans         # list the orphan files
 *   polly coverage --no-mutate       # skip the Stryker target check
 *   polly coverage --config <path>   # explicit coverage.config.ts
 *   bun test --coverage | polly coverage --stdin
 */

import { loadCoverageConfig } from "./discover";
import { type CoverageFindings, enforceCoverage, hasFailure, parseCoverageTable } from "./enforce";
import { type MutateTargetReport, validateMutateTargets } from "./mutate-targets";

interface Args {
  root: string;
  configPath?: string;
  strictOrphans: boolean;
  listOrphans: boolean;
  stdin: boolean;
  mutate: boolean;
  help: boolean;
}

function parseArgs(argv: string[]): Args {
  const flag = (name: string) => argv.includes(name);
  const argValue = (name: string): string | undefined => {
    const i = argv.indexOf(name);
    return i >= 0 ? argv[i + 1] : undefined;
  };
  const strictOrphans = flag("--strict-orphans");
  return {
    root: process.cwd(),
    configPath: argValue("--config"),
    strictOrphans,
    listOrphans: strictOrphans || flag("--orphans"),
    stdin: flag("--stdin"),
    mutate: !flag("--no-mutate"),
    help: flag("--help") || flag("-h"),
  };
}

async function readStdin(): Promise<string> {
  const chunks: string[] = [];
  for await (const chunk of Bun.stdin.stream()) chunks.push(new TextDecoder().decode(chunk));
  return chunks.join("");
}

function reportPolicy(f: CoverageFindings): void {
  for (const m of f.missingExemptFiles) {
    process.stderr.write(`❌ exempt source missing: ${m}\n`);
  }
  for (const { file, claimedBy } of f.missingClaimedBy) {
    process.stderr.write(`❌ ${file} → claimedBy missing: ${claimedBy}\n`);
  }
  for (const s of f.staleExempts) {
    process.stderr.write(`❌ exempt file now meets the floor — promote it: ${s}\n`);
  }
  for (const v of f.violations) {
    process.stderr.write(
      `❌ ${v.file} ${v.metric}=${v.observed.toFixed(2)}% (need ≥ ${v.required}%)\n`
    );
  }
}

function reportOrphans(f: CoverageFindings, args: Args): void {
  if (f.orphans.length === 0) return;
  process.stderr.write(
    `${args.strictOrphans ? "❌" : "⚠️ "} ${f.orphans.length} src file(s) no unit test imports\n`
  );
  if (args.listOrphans) for (const o of f.orphans) process.stderr.write(`   ${o}\n`);
  else process.stderr.write("   --orphans to list, --strict-orphans to fail\n");
}

function reportMutate(report: MutateTargetReport): void {
  if (report.issues.length === 0) return;
  process.stderr.write(`❌ ${report.issues.length} Stryker target(s) resolve to no files:\n`);
  for (const i of report.issues) {
    process.stderr.write(`   ${i.config} [${i.field}] ${i.pattern}\n`);
  }
}

function showHelp(): void {
  process.stdout.write(
    "polly coverage — coverage policy, orphan detection, Stryker target validation\n\n" +
      "  --strict-orphans   fail on source no unit test imports\n" +
      "  --orphans          list orphan files\n" +
      "  --no-mutate        skip the Stryker mutate/testFiles check\n" +
      "  --config <path>    explicit coverage.config.ts\n" +
      "  --stdin            read a `bun test --coverage` table from stdin\n"
  );
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    showHelp();
    return;
  }

  const { config, source } = await loadCoverageConfig(args.root, args.configPath);
  const srcDir = config.srcDir ?? "src";

  const findings = args.stdin
    ? await import("./enforce").then(async (m) => {
        const rows = parseCoverageTable(await readStdin(), srcDir);
        return m.evaluateCoverage(args.root, rows, config);
      })
    : await enforceCoverage(args.root, config);

  reportPolicy(findings);
  reportOrphans(findings, args);

  let mutate: MutateTargetReport = { configs: [], issues: [] };
  if (args.mutate) {
    mutate = await validateMutateTargets(args.root);
    reportMutate(mutate);
  }

  const failed = hasFailure(findings, args.strictOrphans) || mutate.issues.length > 0;
  if (!failed) {
    const mode = findings.enforced ? `floor enforced` : "report-only (no defaultThreshold)";
    const where = source ? "" : " — zero-config";
    const orphanNote = findings.orphans.length ? `, ${findings.orphans.length} orphan` : "";
    const mutateNote = mutate.configs.length
      ? `, ${mutate.configs.length} stryker config(s) ok`
      : "";
    process.stdout.write(
      `✅ coverage ok — ${findings.rowCount} src files, ${mode}${where}${orphanNote}${mutateNote}\n`
    );
  }
  process.exit(failed ? 1 : 0);
}

await main();
