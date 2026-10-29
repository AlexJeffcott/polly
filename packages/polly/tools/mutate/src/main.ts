/**
 * `polly mutate` — run mutation testing and surface useless/redundant
 * tests (the inverse reading of the kill matrix). Thin dispatcher over the
 * reusable functions in this directory.
 */
import { resolve } from "node:path";
import { findStrykerConfigs } from "../../test/src/coverage-policy/mutate-targets.ts";
import { parseMutateArgs } from "./args.ts";
import { resolveMutateConfig } from "./config.ts";
import { decide, status } from "./decisions.ts";
import { buildDb, loadMutationReport } from "./ingest.ts";
import { initConfig } from "./init.ts";
import { migrateConfig } from "./migrate.ts";
import { reportFromFile, resolveEngine, runBunEngine } from "./run.ts";
import { verifyMatrix } from "./verify-matrix.ts";

const HELP = `polly mutate — mutation testing + useless-test detection

Mutation testing breaks your code one edit at a time and checks whether a test
fails; a surviving mutant is a line no test pins down — a truer signal than line
coverage, which only proves a line ran. Read the same kill matrix the other way
and it also finds dead weight: redundant tests (every kill caught elsewhere) and
theatre (code a test ran but never actually checked). How the matrix is built:
https://github.com/AlexJeffcott/polly/blob/main/packages/polly/tools/mutate/README.md

Usage:
  polly mutate init [--force]        Scaffold a polly.mutate.ts for this project
  polly mutate migrate [--write]     Convert stryker.conf.json to polly.mutate.ts (prints it
                                     unless --write; --force overwrites an existing one)
  polly mutate [run]                 Run mutation testing, then print the useless-test report
  polly mutate report                Print the report from an existing mutation.json
  polly mutate decisions             Review verdicts: needs-review / stale / settled
  polly mutate decisions decide <file> <keep|prune|rewrite|investigate> "<rationale>"
  polly mutate verify [--run]        Assert the kill-matrix contract (exit 1 on drift)
  polly mutate help                  Show this help

Flags:
  --config <path>     polly.mutate.ts, or a stryker.conf.json (default: ./polly.mutate.ts,
                      else the discovered Stryker config, deprecated)
  --report <path>     mutation report JSON (default: reports/mutation/mutation.json)
  --decisions <path>  verdict log (default: .polly/test-debt/decisions.jsonl)
  --db <path>         intermediate SQLite (default: in-memory)
  --no-report         'run' only — skip the analysis
  --files <a,b>       mutate only these files (globs and :from-to ranges allowed)
  --since <git-ref>   mutate only targets changed since the ref
  --in-tree           run tests in the project dir, not a scratch cwd
  --concurrency <n>   parallel test processes (default: config, else cores-1)
  --mode <fast|matrix> fast stops each run at the first failing test (default
                      unless the config sets mode);
                      matrix runs every test and records each killer (the kill matrix)
  --coverage <dynamic|static> dynamic (default) runs one probed pass to find the
                      tests that run each mutant, and marks unrun code NoCoverage;
                      static runs every test file that imports the target
  --no-cache          rerun targets whose inputs are unchanged
  --no-typecheck      run mutants the project's tsconfig rejects (default: report
                      them CompileError without a run; needs typescript-7)
  --contracts <off|ensures|all> POLLY_CONTRACTS for every test process: a false
                      requires/ensures throws, so each contract kills the mutants
                      that falsify it (default all; ensures leaves requires inert;
                      a baseline that violates a contract stops the run)
  -h, --help

The redundancy/subsumption sections need a COMPLETE kill matrix ('--mode matrix').
Without it the report degrades
to score + gaps + theatre; 'polly mutate verify' diagnoses the matrix
('verify --run' runs a matrix pass first).`;

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

async function init(cwd: string, force: boolean): Promise<number> {
  const result = await initConfig(cwd, { force });
  if (!result.created) {
    console.log(`${result.configPath} already exists. Re-run with --force to overwrite.`);
    return 1;
  }
  console.log(`✓ wrote ${result.configPath}`);
  console.log(`  import:  ${result.specifier}`);
  console.log(`  targets: ${result.mutate.join(", ")}`);
  console.log(`  tests:   ${result.testGlob}`);
  for (const w of result.warnings) console.log(`  ⚠ ${w}`);
  console.log("\nNext: polly mutate run");
  return 0;
}

async function migrate(cwd: string, args: ReturnType<typeof parseMutateArgs>): Promise<number> {
  const strykerPath = args.config
    ? resolve(cwd, args.config)
    : ((await findStrykerConfigs(cwd))[0] ?? null);
  if (!strykerPath) {
    console.log("no stryker.conf.json found — pass --config <path>");
    return 1;
  }
  const result = await migrateConfig(strykerPath, { write: args.write, force: args.force });
  for (const n of result.notes) console.log(`note: ${n}`);
  if (!args.write) {
    console.log(`\n// ${result.path}\n${result.source}`);
    console.log("Re-run with --write to write it.");
    return 0;
  }
  if (!result.written) {
    console.log(`${result.path} already exists. Re-run with --force to overwrite.`);
    return 1;
  }
  console.log(`✓ wrote ${result.path}`);
  console.log(`  ${strykerPath} is no longer read once polly.mutate.ts exists; delete it.`);
  return 0;
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: a flat verb dispatcher — the branches are the command surface.
async function main(): Promise<number> {
  const args = parseMutateArgs(process.argv.slice(2));
  if (args.help) {
    console.log(HELP);
    return 0;
  }

  const cwd = process.cwd();
  // init and migrate write the config; they must work before one loads.
  if (args.verb === "init") return await init(cwd, args.force);
  if (args.verb === "migrate") return await migrate(cwd, args);
  const cfg = await resolveMutateConfig(cwd, args);

  switch (args.verb) {
    case "run": {
      resolveEngine(args);
      const code = await runBunEngine(cfg, args);
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
      if (args.run) {
        resolveEngine(args);
        await runBunEngine(cfg, { ...args, mode: "matrix" });
      }
      const result = await verifyMatrix({ reportPath: cfg.reportPath });
      console.log("\nKill-matrix contract:");
      for (const c of result.checks) console.log(`  ${c.ok ? "✓" : "✗"} ${c.name}  (${c.detail})`);
      if (!result.ok) {
        console.log(
          "\n✗ Contract broken. Re-check the Bun version: matrix mode reads Bun's junit output (engine/junit.ts)."
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
