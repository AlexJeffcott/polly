/**
 * Orchestration for `polly mutate run` / `report`: spawn Stryker, then read the
 * mutation report and produce the useless-test analysis — gating the redundancy
 * /subsumption sections on a complete (no-bail) kill matrix.
 */
import { relative, resolve } from "node:path";
import type { MutateArgs } from "./args.ts";
import type { MutateConfig } from "./config.ts";
import { mutationScore, runEngine } from "./engine/index.ts";
import { engineConfigFromStryker } from "./engine-config.ts";
import { buildDb, loadMutationReport } from "./ingest.ts";
import { report } from "./report.ts";
import { isMatrixComplete } from "./verify-matrix.ts";

/** Run Stryker against the resolved config. Inherits stdio for the live reporter; returns the exit code. */
export async function runStryker(cfg: MutateConfig): Promise<number> {
  // Pass the config only when it is NOT the auto-discoverable root
  // stryker.conf.json — that keeps a bare repo run identical to `stryker run`.
  // Stryker takes it as a positional argument; it rejects `--configFile`.
  const autoDiscoverable = cfg.strykerConfigPath === resolve(cfg.cwd, "stryker.conf.json");
  const configArg = cfg.strykerConfigPath && !autoDiscoverable ? [cfg.strykerConfigPath] : [];
  const proc = Bun.spawn(["bunx", "stryker", "run", ...configArg], {
    cwd: cfg.cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  return await proc.exited;
}

export type EngineName = "stryker" | "bun";

export function resolveEngine(args: MutateArgs): EngineName {
  const engine = args.engine ?? "stryker";
  if (engine === "stryker" || engine === "bun") return engine;
  throw new Error(`unknown --engine "${engine}" (expected stryker or bun)`);
}

/** Run the Bun-native engine and print a per-target summary. Returns the exit code. */
export async function runBunEngine(cfg: MutateConfig, args: MutateArgs): Promise<number> {
  const engineCfg = await engineConfigFromStryker(cfg, args);
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

  console.log("\nfile | tests | killed | survived | timeout | no-cov | other | score");
  const all = result.targets.flatMap((t) => t.results);
  for (const t of result.targets) {
    const count = (s: string) => t.results.filter((r) => r.status === s).length;
    const other =
      t.results.length -
      count("Killed") -
      count("Survived") -
      count("Timeout") -
      count("NoCoverage");
    const score = mutationScore(t.results);
    console.log(
      [
        relative(engineCfg.cwd, t.file),
        t.coveringTests.length,
        count("Killed"),
        count("Survived"),
        count("Timeout"),
        count("NoCoverage"),
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
  return 0;
}

/** Build the useless-test report from an existing mutation.json (no Stryker run). */
export async function reportFromFile(cfg: MutateConfig): Promise<string> {
  if (!(await Bun.file(cfg.reportPath).exists())) {
    throw new Error(
      `no mutation report at ${cfg.reportPath}. Run 'polly mutate run' (or 'bun run mutation') first, or pass --report <path>.`
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

/**
 * If the Stryker config doesn't already load polly's verify-primitive ignorer,
 * return a one-line tip. The ignorer must be in the config before the run (it's
 * read at Stryker startup), so this advises rather than mutating the user's config.
 */
export async function presetAdvisory(cfg: MutateConfig): Promise<string | null> {
  if (!cfg.strykerConfigPath?.endsWith(".json")) return null;
  try {
    const conf = (await Bun.file(cfg.strykerConfigPath).json()) as unknown as {
      plugins?: string[];
    };
    if ((conf.plugins ?? []).includes("@fairfox/polly/stryker")) return null;
    return (
      "Tip: spread pollyStrykerPreset (from @fairfox/polly/stryker) into your Stryker config — " +
      "verify primitives (requires/ensures/…) are runtime no-ops and their mutants always survive, " +
      "dragging the score down with noise. See polly#143."
    );
  } catch {
    return null;
  }
}
