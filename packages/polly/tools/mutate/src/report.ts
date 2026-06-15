/**
 * Test-debt report: derive the three signals from the kill matrix.
 *
 *   gaps        survived mutants — code no test pins (the Stryker direction)
 *   redundancy  tests/files whose every kill is also caught elsewhere
 *   theatre     covered-but-survived — code a test runs but no test detects
 *               (the Survived status under coverageAnalysis "all")
 *
 * Redundancy is reported at BOTH file and case level. Decisions are keyed at
 * file level (stable identity); case level is the drill-down.
 */
import type { Database } from "bun:sqlite";
import { buildDb, loadMutationReport, queryAll, queryGet } from "./ingest.ts";

type SubsumedCase = { file: string; name: string; total: number };
type LineCount = { line: number; mutator: string; n: number };

/** Greedy set cover: smallest set of `units` whose kill-sets cover all killed mutants. */
// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: a textbook greedy set-cover loop — clearer whole than split.
function greedyCover(units: Map<string, Set<string>>, universe: Set<string>): string[] {
  const remaining = new Set(universe);
  const chosen: string[] = [];
  const pool = new Map([...units].map(([k, v]) => [k, new Set(v)]));
  while (remaining.size > 0) {
    let best: string | null = null;
    let bestGain = 0;
    for (const [unit, set] of pool) {
      let gain = 0;
      for (const m of set) if (remaining.has(m)) gain++;
      if (gain > bestGain) {
        bestGain = gain;
        best = unit;
      }
    }
    if (best === null || bestGain === 0) break; // remaining mutants killed by nobody (shouldn't happen for killed set)
    chosen.push(best);
    for (const m of pool.get(best) ?? []) remaining.delete(m);
    pool.delete(best);
  }
  return chosen;
}

// biome-ignore lint/complexity/noExcessiveCognitiveComplexity: one report builder emitting all sections in order — splitting would scatter the shared db/out.
export function report(db: Database, opts: { matrixComplete?: boolean } = {}): string {
  // Defaults to true so `report(db)` is byte-identical to before (the parity
  // guard depends on this). When false — the kill matrix is partial (an
  // unpatched/bail runner) — the redundancy/subsumption sections would lie, so
  // they are suppressed and a warning shown; score/gaps/theatre still hold.
  const matrixComplete = opts.matrixComplete ?? true;
  const out: string[] = [];
  const p = (s = "") => out.push(s);

  // --- summary ---
  const tot = queryGet<{
    n: number;
    killed: number;
    survived: number;
    timeout: number;
    nocov: number;
  }>(
    db,
    "SELECT count(*) n, sum(status='Killed') killed, sum(status='Survived') survived, sum(status='Timeout') timeout, sum(status='NoCoverage') nocov FROM mutants"
  ) ?? { n: 0, killed: 0, survived: 0, timeout: 0, nocov: 0 };
  const nTests = queryGet<{ n: number }>(db, "SELECT count(*) n FROM tests")?.n ?? 0;
  const detected = tot.killed + tot.timeout;
  const score = ((detected / (tot.n - tot.nocov || 1)) * 100).toFixed(1);
  p(
    `MUTATION  score ${score}%   ${tot.killed} killed · ${tot.timeout} timeout · ${tot.survived} survived · ${tot.nocov} no-coverage   (${tot.n} mutants, ${nTests} tests)`
  );

  if (matrixComplete) {
    // --- kill-multiplicity: how much slack is in the matrix ---
    const mult = queryAll<{ bucket: string; n: number }>(
      db,
      `
			SELECT CASE WHEN c=1 THEN '1' WHEN c=2 THEN '2' WHEN c BETWEEN 3 AND 5 THEN '3-5' ELSE '6+' END bucket, count(*) n
			FROM (SELECT mutant_id, count(*) c FROM kills GROUP BY mutant_id)
			GROUP BY bucket ORDER BY min(c)`
    );
    p(`\nKILL MULTIPLICITY  (killers per killed mutant — higher = more redundancy slack)`);
    for (const r of mult) p(`  killed by ${String(r.bucket).padStart(3)} test(s): ${r.n}`);

    // --- redundancy ratio via greedy cover (case + file) ---
    const universe = new Set(
      queryAll<{ mutant_id: string }>(db, "SELECT DISTINCT mutant_id FROM kills").map(
        (r) => r.mutant_id
      )
    );
    const byTest = new Map<string, Set<string>>();
    for (const r of queryAll<{ test_id: string; mutant_id: string }>(
      db,
      "SELECT test_id, mutant_id FROM kills"
    )) {
      const set = byTest.get(r.test_id) ?? new Set<string>();
      byTest.set(r.test_id, set);
      set.add(r.mutant_id);
    }
    const byFile = new Map<string, Set<string>>();
    for (const r of queryAll<{ file: string; mid: string }>(
      db,
      "SELECT t.file file, k.mutant_id mid FROM kills k JOIN tests t ON t.id=k.test_id"
    )) {
      const set = byFile.get(r.file) ?? new Set<string>();
      byFile.set(r.file, set);
      set.add(r.mid);
    }
    const caseCover = greedyCover(byTest, universe);
    const fileCover = greedyCover(byFile, universe);
    p(`\nREDUNDANCY RATIO  (tests that kill something ÷ minimal covering set)`);
    p(
      `  case level: ${byTest.size} killing tests → ${caseCover.length} needed   (${(byTest.size / Math.max(1, caseCover.length)).toFixed(2)}×, ~${byTest.size - caseCover.length} prunable)`
    );
    p(
      `  file level: ${byFile.size} killing files → ${fileCover.length} needed   (${(byFile.size / Math.max(1, fileCover.length)).toFixed(2)}×, ~${byFile.size - fileCover.length} prunable)`
    );

    // --- fully subsumed FILES (every mutant they kill is killed elsewhere too) ---
    const subsumedFiles = queryAll<{ file: string; kills: number }>(
      db,
      `
			WITH file_kill AS (SELECT DISTINCT t.file file, k.mutant_id mid FROM kills k JOIN tests t ON t.id=k.test_id),
			     owner AS (SELECT mid, count(DISTINCT file) nf, min(file) only_file FROM file_kill GROUP BY mid)
			SELECT fk.file, count(DISTINCT fk.mid) kills,
			       sum(CASE WHEN o.nf=1 THEN 1 ELSE 0 END) unique_kills
			FROM file_kill fk JOIN owner o ON o.mid=fk.mid
			GROUP BY fk.file HAVING unique_kills=0 ORDER BY kills DESC`
    );
    p(`\nSUBSUMED FILES  (file-level identity — safe-to-review deletion candidates)`);
    if (subsumedFiles.length === 0)
      p(`  none — every test file kills at least one mutant no other file catches`);
    for (const r of subsumedFiles) p(`  ${r.file}  (${r.kills} kills, 0 unique)`);

    // --- fully subsumed CASES (drill-down) ---
    const subsumedCases = queryAll<SubsumedCase>(
      db,
      `
			WITH mk AS (SELECT mutant_id, count(*) c FROM kills GROUP BY mutant_id),
			     tk AS (SELECT test_id, count(*) total, sum(CASE WHEN mk.c=1 THEN 1 ELSE 0 END) uniq
			            FROM kills JOIN mk USING(mutant_id) GROUP BY test_id)
			SELECT t.file, t.name, tk.total FROM tk JOIN tests t ON t.id=tk.test_id
			WHERE tk.total>0 AND tk.uniq=0 ORDER BY t.file, tk.total DESC`
    );
    const byFileCases = new Map<string, SubsumedCase[]>();
    for (const r of subsumedCases) {
      const rows = byFileCases.get(r.file) ?? [];
      byFileCases.set(r.file, rows);
      rows.push(r);
    }
    p(
      `\nSUBSUMED CASES  (${subsumedCases.length} individual tests whose every kill is caught elsewhere)`
    );
    for (const [file, rows] of byFileCases) {
      p(`  ${file}`);
      for (const r of rows) p(`      “${r.name}” (${r.total} kills, 0 unique)`);
    }
  } else {
    p(`\n⚠ KILL MATRIX INCOMPLETE — redundancy/subsumption analysis suppressed.`);
    p(`  Every mutant has at most one recorded killer, so "which tests are redundant"`);
    p(`  cannot be derived. This needs the no-bail patched Bun runner (not shipped with`);
    p(
      `  @fairfox/polly). Run 'polly mutate verify' to diagnose. Score/gaps/theatre below still hold.`
    );
  }

  // Under coverageAnalysis "all", Stryker classifies a non-killed mutant as
  // NoCoverage (no test runs it — a true gap) or Survived (a test runs it but
  // nothing detects the mutation — theatre). That status split IS the
  // gap/theatre distinction; it requires coverage to be on (see README).
  const srcFile = queryGet<{ file: string }>(db, "SELECT file FROM mutants LIMIT 1")?.file;

  // --- gaps: code no test even executes ---
  const gaps = queryAll<LineCount>(
    db,
    "SELECT line, mutator, count(*) n FROM mutants WHERE status='NoCoverage' GROUP BY line, mutator ORDER BY line"
  );
  const gapTotal = gaps.reduce((a, r) => a + r.n, 0);
  p(`\nGAPS  (NoCoverage — no test executes this code: ${gapTotal})`);
  if (gapTotal === 0) p(`  none — every mutable location is reached by some test`);
  for (const r of gaps) p(`  ${srcFile}:${r.line}  ${r.mutator}${r.n > 1 ? ` ×${r.n}` : ""}`);

  // --- theatre: covered but survived ---
  const theatre = queryAll<LineCount>(
    db,
    "SELECT line, mutator, count(*) n FROM mutants WHERE status='Survived' GROUP BY line, mutator ORDER BY line"
  );
  const theatreTotal = theatre.reduce((a, r) => a + r.n, 0);
  p(`\nTHEATRE  (Survived — code is covered but no test detects the mutation: ${theatreTotal})`);
  if (theatreTotal === 0) p(`  none`);
  for (const r of theatre) p(`  ${srcFile}:${r.line}  ${r.mutator}${r.n > 1 ? ` ×${r.n}` : ""}`);

  return out.join("\n");
}

if (import.meta.main) {
  const reportPath = process.argv[2] ?? "reports/mutation/mutation.json";
  const db = buildDb(await loadMutationReport(reportPath), "reports/test-debt.sqlite");
  console.log(report(db));
  db.close();
}
