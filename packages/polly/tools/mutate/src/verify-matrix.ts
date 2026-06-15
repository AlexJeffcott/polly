/**
 * Verification artefact for the kill-matrix contract.
 *
 * The whole useless-test analysis rests on one fact: the patched bun runner
 * emits a COMPLETE kill matrix — every test that detects a mutant appears in
 * killedBy, not just the first. That depends on a pinned pair: (Bun version,
 * plugin version + our patch). A Bun upgrade that changes JUnit output, or a
 * patch that stops applying, would silently collapse killedBy to one id each —
 * a green board with the redundancy signal quietly dead (the classic trap).
 *
 * `verifyMatrix` runs the full contract and returns the result; `isMatrixComplete`
 * is the side-effect-free gate the report path consults to decide whether the
 * redundancy/subsumption sections are trustworthy. Run the CLI form after any
 * bump of Bun or the plugin:
 *
 *   polly mutate verify          # uses the existing report
 *   polly mutate verify --run    # runs stryker first
 */
import { loadMutationReport, type MutationReport } from "./ingest.ts";

const DEFAULT_REPORT = "reports/mutation/mutation.json";

export interface MatrixCheck {
  ok: boolean;
  checks: { name: string; ok: boolean; detail: string }[];
}

/**
 * Side-effect-free gate: is the kill matrix trustworthy for redundancy /
 * subsumption analysis? True only when
 *   (a) some killed mutant has >1 killer — proof the no-bail patched runner
 *       recorded EVERY killer, not just the first (verifyMatrix check #4), and
 *   (b) coverage was collected — not every mutant is NoCoverage, which would
 *       mean the coverage dump broke (verifyMatrix check #5).
 * Without both, REDUNDANCY/SUBSUMED would be computed off a partial matrix and
 * lie, so the report path falls back to score + gaps + theatre only.
 */
export function isMatrixComplete(report: MutationReport): boolean {
  const mutants = Object.values(report.files).flatMap((f) => f.mutants);
  if (mutants.length === 0) return false;
  const killed = mutants.filter((m) => m.status === "Killed");
  const multiKiller = killed.some((m) => (m.killedBy ?? []).length > 1);
  const noCov = mutants.filter((m) => m.status === "NoCoverage").length;
  const coverageCollected = noCov < mutants.length;
  return multiKiller && coverageCollected;
}

/**
 * Run the full kill-matrix contract (all five checks), optionally running a
 * fresh Stryker pass first. Returns the result rather than exiting, so callers
 * decide what to do with it; the `import.meta.main` wrapper prints and sets the
 * exit code.
 */
export async function verifyMatrix(
  opts: { reportPath?: string; run?: boolean; strykerConfig?: string } = {}
): Promise<MatrixCheck> {
  const reportPath = opts.reportPath ?? DEFAULT_REPORT;

  if (opts.run) {
    console.log("Running mutation pass (this can take many minutes for a large mutate set)...");
    const cmd = [
      "bunx",
      "stryker",
      "run",
      ...(opts.strykerConfig ? ["--configFile", opts.strykerConfig] : []),
    ];
    const proc = Bun.spawn(cmd, { stdout: "inherit", stderr: "inherit" });
    const code = await proc.exited;
    if (code !== 0) {
      return { ok: false, checks: [{ name: "stryker run", ok: false, detail: `exited ${code}` }] };
    }
  }

  if (!(await Bun.file(reportPath).exists())) {
    return {
      ok: false,
      checks: [
        {
          name: "report exists",
          ok: false,
          detail: `no report at ${reportPath}. Run with --run, or 'bun run mutation' first.`,
        },
      ],
    };
  }

  const report = await loadMutationReport(reportPath);
  const checks: { name: string; ok: boolean; detail: string }[] = [];
  const add = (name: string, ok: boolean, detail: string) => checks.push({ name, ok, detail });

  // 1. schema present
  add("schema version present", !!report.schemaVersion, `schemaVersion=${report.schemaVersion}`);

  // 2. testFiles keyed by real paths, not the "" bucket (file-level identity intact)
  const tfKeys = Object.keys(report.testFiles ?? {});
  const realPaths = tfKeys.filter((k) => k && k !== "(unknown)");
  add(
    "testFiles keyed by real paths",
    realPaths.length > 0 && !tfKeys.includes(""),
    `${realPaths.length} file(s): ${realPaths.slice(0, 2).join(", ")}${realPaths.length > 2 ? "…" : ""}`
  );

  // 3. test ids resolve
  const testIds = new Set(
    Object.values(report.testFiles ?? {}).flatMap((tf) => tf.tests.map((t) => t.id))
  );
  const mutants = Object.values(report.files).flatMap((f) => f.mutants);
  const killed = mutants.filter((m) => m.status === "Killed");
  const danglingKb = killed.filter((m) => (m.killedBy ?? []).some((id) => !testIds.has(id)));
  add(
    "every killedBy id resolves to a test",
    danglingKb.length === 0,
    `${danglingKb.length} dangling`
  );

  // 4. THE contract: a complete matrix means some killed mutant has >1 killer.
  //    If bail silently re-engaged, every killedBy would have length 1.
  const withKb = killed.filter((m) => (m.killedBy ?? []).length > 0);
  const multi = killed.filter((m) => (m.killedBy ?? []).length > 1);
  add(
    "killed mutants carry killedBy",
    killed.length > 0 && withKb.length === killed.length,
    `${withKb.length}/${killed.length}`
  );
  add(
    "matrix is complete (no-bail): >1 killer exists",
    multi.length > 0,
    `${multi.length} mutant(s) killed by >1 test — collapses to 0 if bail re-engages`
  );

  // 5. coverage extraction works: if the afterAll dump fails, the coverage map is
  //    empty and Stryker marks EVERY mutant NoCoverage (theatre/gap split dies).
  const noCov = mutants.filter((m) => m.status === "NoCoverage").length;
  add(
    "coverage collected (not all NoCoverage)",
    noCov < mutants.length,
    `${noCov}/${mutants.length} NoCoverage — all-NoCoverage means the coverage dump broke`
  );

  return { ok: checks.every((c) => c.ok), checks };
}

if (import.meta.main) {
  const result = await verifyMatrix({ run: process.argv.includes("--run") });
  console.log("\nKill-matrix contract:");
  for (const c of result.checks) {
    console.log(`  ${c.ok ? "✓" : "✗"} ${c.name}  (${c.detail})`);
  }
  if (!result.ok) {
    console.log(
      "\n✗ Contract broken. The pinned pair has drifted — re-check Bun version and that the patch applies (bun install)."
    );
    process.exit(1);
  }
  console.log("\n✓ Kill-matrix contract holds.");
}
