#!/usr/bin/env bun
/**
 * `polly mutate` — run Stryker mutation testing and surface useless/redundant
 * tests (the inverse reading of the kill matrix). Thin dispatcher over the
 * reusable functions in this directory.
 */
import { parseMutateArgs } from "./args.ts";
import { resolveMutateConfig } from "./config.ts";
import { decide, status } from "./decisions.ts";
import { buildDb, loadMutationReport } from "./ingest.ts";
import { initConfig } from "./init.ts";
import { presetAdvisory, reportFromFile, runStryker } from "./run.ts";
import { verifyMatrix } from "./verify-matrix.ts";

const HELP = `polly mutate — mutation testing + useless-test detection

Mutation testing breaks your code one edit at a time and checks whether a test
fails; a surviving mutant is a line no test pins down — a truer signal than line
coverage, which only proves a line ran. Read the same kill matrix the other way
and it also finds dead weight: redundant tests (every kill caught elsewhere) and
theatre (code a test ran but never actually checked). How the matrix is built:
tools/mutate/README.md.

Usage:
  polly mutate init [--force]        Scaffold a stryker.conf.json for this project
  polly mutate [run]                 Run Stryker, then print the useless-test report
  polly mutate report                Print the report from an existing mutation.json
  polly mutate decisions             Review verdicts: needs-review / stale / settled
  polly mutate decisions decide <file> <keep|prune|rewrite|investigate> "<rationale>"
  polly mutate verify [--run]        Assert the kill-matrix contract (exit 1 on drift)
  polly mutate help                  Show this help

Flags:
  --config <path>     Stryker config (default: auto-discovered)
  --report <path>     mutation report JSON (default: reports/mutation/mutation.json)
  --decisions <path>  verdict log (default: .polly/test-debt/decisions.jsonl)
  --db <path>         intermediate SQLite (default: in-memory)
  --no-report         'run' only — skip the analysis
  -h, --help

The redundancy/subsumption sections need a COMPLETE kill matrix (the no-bail
patched Bun runner). Without it the report degrades to score + gaps + theatre;
'polly mutate verify' diagnoses the matrix.`;

async function openDb(
  reportPath: string,
  dbPath: string
): Promise<ReturnType<typeof buildDb> | null> {
  if (!(await Bun.file(reportPath).exists())) {
    console.log(
      `no mutation report at ${reportPath}. Run 'polly mutate run' first, or pass --report <path>.`
    );
    return null;
  }
  return buildDb(await loadMutationReport(reportPath), dbPath);
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: a flat verb dispatcher — the branches are the command surface.
async function main(): Promise<number> {
  const args = parseMutateArgs(process.argv.slice(2));
  if (args.help) {
    console.log(HELP);
    return 0;
  }

  const cwd = process.cwd();
  const cfg = await resolveMutateConfig(cwd, args);

  switch (args.verb) {
    case "init": {
      const result = await initConfig(cwd, { force: args.force });
      if (!result.created) {
        console.log(
          `stryker.conf.json already exists at ${result.configPath}. Re-run with --force to overwrite.`
        );
        return 1;
      }
      console.log(`✓ wrote ${result.configPath}`);
      console.log(`  plugin:    ${result.pluginRef}`);
      console.log(`  mutate:    ${result.mutate.join(", ")}`);
      console.log(`  testFiles: ${result.testGlob}`);
      for (const w of result.warnings) console.log(`  ⚠ ${w}`);
      console.log("\nNext: polly mutate run");
      return 0;
    }

    case "run": {
      const tip = await presetAdvisory(cfg);
      if (tip) console.log(`${tip}\n`);
      const code = await runStryker(cfg);
      if (code !== 0) return code;
      if (args.noReport) return 0;
      console.log(`\n${await reportFromFile(cfg)}`);
      return 0;
    }

    case "report": {
      console.log(await reportFromFile(cfg));
      return 0;
    }

    case "decisions": {
      const db = await openDb(cfg.reportPath, cfg.dbPath);
      if (!db) return 1;
      try {
        if (args.rest[0] === "decide") {
          const [, file, verdict, ...r] = args.rest;
          if (!file || !verdict) {
            console.log(
              'usage: polly mutate decisions decide <file> <keep|prune|rewrite|investigate> "<rationale>"'
            );
            return 1;
          }
          await decide(file, verdict, r.join(" ").replace(/^"|"$/g, ""), db, cfg.decisionsPath);
        } else {
          console.log(await status(db, cfg.decisionsPath));
        }
      } finally {
        db.close();
      }
      return 0;
    }

    case "verify": {
      const result = await verifyMatrix({
        reportPath: cfg.reportPath,
        run: args.run,
        strykerConfig: cfg.strykerConfigPath ?? undefined,
      });
      console.log("\nKill-matrix contract:");
      for (const c of result.checks) console.log(`  ${c.ok ? "✓" : "✗"} ${c.name}  (${c.detail})`);
      if (!result.ok) {
        console.log(
          "\n✗ Contract broken. The pinned pair has drifted — re-check Bun version and that the patch applies (bun install)."
        );
        return 1;
      }
      console.log("\n✓ Kill-matrix contract holds.");
      return 0;
    }

    default:
      console.log(`Unknown subcommand: ${args.verb}\n`);
      console.log(HELP);
      return 1;
  }
}

main()
  .then((code) => process.exit(code))
  .catch((err) => {
    console.log(`\n❌ ${err instanceof Error ? err.message : String(err)}`);
    process.exit(1);
  });
