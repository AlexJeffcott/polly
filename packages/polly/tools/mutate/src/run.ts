/**
 * Orchestration for `polly mutate run` / `report`: spawn Stryker, then read the
 * mutation report and produce the useless-test analysis — gating the redundancy
 * /subsumption sections on a complete (no-bail) kill matrix.
 */
import { resolve } from "node:path";
import type { MutateConfig } from "./config.ts";
import { buildDb, loadMutationReport } from "./ingest.ts";
import { report } from "./report.ts";
import { isMatrixComplete } from "./verify-matrix.ts";

/** Run Stryker against the resolved config. Inherits stdio for the live reporter; returns the exit code. */
export async function runStryker(cfg: MutateConfig): Promise<number> {
  // Pass --configFile only when the located config is NOT the auto-discoverable
  // root stryker.conf.json — that keeps a bare repo run identical to `stryker run`.
  const autoDiscoverable = cfg.strykerConfigPath === resolve(cfg.cwd, "stryker.conf.json");
  const configFlag =
    cfg.strykerConfigPath && !autoDiscoverable ? ["--configFile", cfg.strykerConfigPath] : [];
  const proc = Bun.spawn(["bunx", "stryker", "run", ...configFlag], {
    cwd: cfg.cwd,
    stdout: "inherit",
    stderr: "inherit",
    stdin: "inherit",
    env: process.env,
  });
  return await proc.exited;
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
