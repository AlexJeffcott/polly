/**
 * Orchestration for `polly mutate run` / `report`: run the Bun-native engine,
 * then read the mutation report and
 * produce the useless-test analysis — gating the redundancy/subsumption
 * sections on a complete (no-bail) kill matrix.
 */
import { relative } from "node:path";
import type { MutateArgs } from "./args.ts";
import type { MutateConfig } from "./config.ts";
import { mutationScore, runEngine } from "./engine/index.ts";
import type { ContractSite, EngineResult } from "./engine/types.ts";
import { engineConfigFor } from "./engine-config.ts";
import { buildDb, loadMutationReport } from "./ingest.ts";
import { report } from "./report.ts";
import { isMatrixComplete } from "./verify-matrix.ts";

/** `--engine` survives for scripts that pass `--engine bun`; Stryker is gone. */
export function resolveEngine(args: MutateArgs): "bun" {
  const engine = args.engine ?? "bun";
  if (engine === "bun") return engine;
  if (engine === "stryker") {
    throw new Error("--engine stryker was removed; the bun engine (the default) replaces it");
  }
  throw new Error(`unknown --engine "${engine}" (expected bun)`);
}

/** The notice printed when the bun engine reads a Stryker config; null for polly.mutate.ts. */
export function deprecationNotice(cfg: MutateConfig): string | null {
  const m = cfg.mutation;
  if (m?.format !== "stryker") return null;
  return [
    `deprecated: reading ${relative(cfg.cwd, m.path) || m.path} — Stryker is no longer supported; its config is read for migration only.`,
    "  'polly mutate migrate --write' writes the equivalent polly.mutate.ts.",
    ...m.notes.map((n) => `  ${n}`),
  ].join("\n");
}

/** `thresholds.break` failure line, or null when the score clears it (or none is set). */
export function thresholdFailure(score: number | null, cfg: MutateConfig): string | null {
  const floor = cfg.mutation?.config.thresholds?.break;
  if (floor === undefined || score === null || score >= floor) return null;
  return `mutation score ${score.toFixed(1)}% is below thresholds.break ${floor}%`;
}

/** Run the Bun-native engine and print a per-target summary. Returns the exit code. */
export async function runBunEngine(cfg: MutateConfig, args: MutateArgs): Promise<number> {
  const notice = deprecationNotice(cfg);
  if (notice) console.log(`${notice}\n`);
  const engineCfg = await engineConfigFor(cfg, args);
  if (engineCfg.targets.length === 0) {
    console.log(
      args.since ? `no mutate targets changed since ${args.since}` : "no mutate targets matched"
    );
    return 0;
  }
  let lastPct = -1;
  const result = await runEngine(engineCfg, {
    log: (line) => console.log(line),
    progress: (done, total) => {
      const pct = Math.floor((100 * done) / total);
      if (pct >= lastPct + 10 || done === total) {
        lastPct = pct;
        console.log(`  ${done}/${total} mutants`);
      }
    },
  });

  console.log("\nfile | tests | killed | survived | timeout | no-cov | invalid | other | score");
  const all = result.targets.flatMap((t) => t.results);
  for (const t of result.targets) {
    const count = (s: string) => t.results.filter((r) => r.status === s).length;
    const other =
      t.results.length -
      count("Killed") -
      count("Survived") -
      count("Timeout") -
      count("NoCoverage") -
      count("CompileError");
    const score = mutationScore(t.results);
    console.log(
      [
        relative(engineCfg.cwd, t.file),
        t.coveringTests.length,
        count("Killed"),
        count("Survived"),
        count("Timeout"),
        count("NoCoverage"),
        count("CompileError"),
        other,
        score === null ? "n/a" : `${score.toFixed(1)}%`,
      ].join(" | ")
    );
  }
  const total = mutationScore(all);
  console.log(
    `\n${all.length} mutants in ${(result.wallMs / 1000).toFixed(1)} s · score ${total === null ? "n/a" : `${total.toFixed(1)}%`} · report ${cfg.reportPath}`
  );
  const stray = result.strayWrites;
  if (stray && stray.mutants.length > 0) {
    console.log(
      `\nwarning: mutant runs wrote ${stray.mutants.length} path(s) into ${stray.root} (not deleted — check, then remove):`
    );
    for (const path of stray.mutants) console.log(`  ${path}`);
  }
  if (result.contractViolations.length > 0) {
    console.log(contractViolationsBlock(result, engineCfg.cwd));
    return 1;
  }
  const failure = thresholdFailure(total, cfg);
  if (failure) {
    console.log(`\n✗ ${failure}`);
    return 1;
  }
  return 0;
}

/**
 * The block printed when a baseline failed through a contract: the unmutated
 * code, under one of its own tests, falsified a requires/ensures. That is a
 * finding about the test or the handler, not about any mutant, so the run
 * stops instead of scoring the target.
 */
export function contractViolationsBlock(result: EngineResult, cwd: string): string {
  const sites = new Map<string, ContractSite>(
    result.targets.flatMap((t) =>
      t.contracts.map((c): [string, ContractSite] => [`${relative(cwd, c.file)}:${c.line}`, c])
    )
  );
  const lines = [
    `\n✗ TEST VIOLATES CONTRACT  (${result.contractViolations.length}; the mutants of these targets did not run)`,
  ];
  for (const v of result.contractViolations) {
    const where = v.contracts.length === 0 ? "" : ` → ${v.contracts.join(", ")}`;
    lines.push(`  ${relative(cwd, v.target)}: ${v.test}${where}`);
    for (const id of v.contracts) {
      const site = sites.get(id);
      if (site) lines.push(`      ${site.primitive}${site.message ? ` “${site.message}”` : ""}`);
    }
  }
  lines.push(
    "  A test drives a handler outside its declared precondition, or a handler breaks its own",
    "  postcondition. Fix the test or the contract; '--contracts ensures' leaves requires inert,",
    "  '--contracts off' restores the no-op primitives."
  );
  return lines.join("\n");
}

/** Build the useless-test report from an existing mutation.json (no engine run). */
export async function reportFromFile(cfg: MutateConfig): Promise<string> {
  if (!(await Bun.file(cfg.reportPath).exists())) {
    throw new Error(
      `no mutation report at ${cfg.reportPath}. Run 'polly mutate run' first, or pass --report <path>.`
    );
  }
  const mreport = await loadMutationReport(cfg.reportPath);
  const db = buildDb(mreport, cfg.dbPath);
  try {
    return report(db, { matrixComplete: isMatrixComplete(mreport) });
  } finally {
    db.close();
  }
}
