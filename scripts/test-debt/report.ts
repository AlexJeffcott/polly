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
import { Database } from "bun:sqlite";
import { buildDb, type MutationReport } from "./ingest.ts";

type Row = Record<string, string | number>;

/** Greedy set cover: smallest set of `units` whose kill-sets cover all killed mutants. */
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
		for (const m of pool.get(best)!) remaining.delete(m);
		pool.delete(best);
	}
	return chosen;
}

export function report(db: Database): string {
	const out: string[] = [];
	const p = (s = "") => out.push(s);

	// --- summary ---
	const tot = db.query("SELECT count(*) n, sum(status='Killed') killed, sum(status='Survived') survived, sum(status='Timeout') timeout, sum(status='NoCoverage') nocov FROM mutants").get() as Row;
	const nTests = (db.query("SELECT count(*) n FROM tests").get() as Row).n as number;
	const detected = (tot.killed as number) + (tot.timeout as number);
	const score = ((detected / ((tot.n as number) - (tot.nocov as number) || 1)) * 100).toFixed(1);
	p(`MUTATION  score ${score}%   ${tot.killed} killed · ${tot.timeout} timeout · ${tot.survived} survived · ${tot.nocov} no-coverage   (${tot.n} mutants, ${nTests} tests)`);

	// --- kill-multiplicity: how much slack is in the matrix ---
	const mult = db.query(`
		SELECT CASE WHEN c=1 THEN '1' WHEN c=2 THEN '2' WHEN c BETWEEN 3 AND 5 THEN '3-5' ELSE '6+' END bucket, count(*) n
		FROM (SELECT mutant_id, count(*) c FROM kills GROUP BY mutant_id)
		GROUP BY bucket ORDER BY min(c)`).all() as Row[];
	p(`\nKILL MULTIPLICITY  (killers per killed mutant — higher = more redundancy slack)`);
	for (const r of mult) p(`  killed by ${String(r.bucket).padStart(3)} test(s): ${r.n}`);

	// --- redundancy ratio via greedy cover (case + file) ---
	const universe = new Set((db.query("SELECT DISTINCT mutant_id FROM kills").all() as Row[]).map((r) => r.mutant_id as string));
	const byTest = new Map<string, Set<string>>();
	for (const r of db.query("SELECT test_id, mutant_id FROM kills").all() as Row[]) {
		const k = r.test_id as string;
		(byTest.get(k) ?? byTest.set(k, new Set()).get(k)!).add(r.mutant_id as string);
	}
	const byFile = new Map<string, Set<string>>();
	for (const r of db.query("SELECT t.file file, k.mutant_id mid FROM kills k JOIN tests t ON t.id=k.test_id").all() as Row[]) {
		const k = r.file as string;
		(byFile.get(k) ?? byFile.set(k, new Set()).get(k)!).add(r.mid as string);
	}
	const caseCover = greedyCover(byTest, universe);
	const fileCover = greedyCover(byFile, universe);
	p(`\nREDUNDANCY RATIO  (tests that kill something ÷ minimal covering set)`);
	p(`  case level: ${byTest.size} killing tests → ${caseCover.length} needed   (${(byTest.size / Math.max(1, caseCover.length)).toFixed(2)}×, ~${byTest.size - caseCover.length} prunable)`);
	p(`  file level: ${byFile.size} killing files → ${fileCover.length} needed   (${(byFile.size / Math.max(1, fileCover.length)).toFixed(2)}×, ~${byFile.size - fileCover.length} prunable)`);

	// --- fully subsumed FILES (every mutant they kill is killed elsewhere too) ---
	const subsumedFiles = db.query(`
		WITH file_kill AS (SELECT DISTINCT t.file file, k.mutant_id mid FROM kills k JOIN tests t ON t.id=k.test_id),
		     owner AS (SELECT mid, count(DISTINCT file) nf, min(file) only_file FROM file_kill GROUP BY mid)
		SELECT fk.file, count(DISTINCT fk.mid) kills,
		       sum(CASE WHEN o.nf=1 THEN 1 ELSE 0 END) unique_kills
		FROM file_kill fk JOIN owner o ON o.mid=fk.mid
		GROUP BY fk.file HAVING unique_kills=0 ORDER BY kills DESC`).all() as Row[];
	p(`\nSUBSUMED FILES  (file-level identity — safe-to-review deletion candidates)`);
	if (subsumedFiles.length === 0) p(`  none — every test file kills at least one mutant no other file catches`);
	for (const r of subsumedFiles) p(`  ${r.file}  (${r.kills} kills, 0 unique)`);

	// --- fully subsumed CASES (drill-down) ---
	const subsumedCases = db.query(`
		WITH mk AS (SELECT mutant_id, count(*) c FROM kills GROUP BY mutant_id),
		     tk AS (SELECT test_id, count(*) total, sum(CASE WHEN mk.c=1 THEN 1 ELSE 0 END) uniq
		            FROM kills JOIN mk USING(mutant_id) GROUP BY test_id)
		SELECT t.file, t.name, tk.total FROM tk JOIN tests t ON t.id=tk.test_id
		WHERE tk.total>0 AND tk.uniq=0 ORDER BY t.file, tk.total DESC`).all() as Row[];
	const byFileCases = new Map<string, Row[]>();
	for (const r of subsumedCases) (byFileCases.get(r.file as string) ?? byFileCases.set(r.file as string, []).get(r.file as string)!).push(r);
	p(`\nSUBSUMED CASES  (${subsumedCases.length} individual tests whose every kill is caught elsewhere)`);
	for (const [file, rows] of byFileCases) {
		p(`  ${file}`);
		for (const r of rows) p(`      “${r.name}” (${r.total} kills, 0 unique)`);
	}

	// Under coverageAnalysis "all", Stryker classifies a non-killed mutant as
	// NoCoverage (no test runs it — a true gap) or Survived (a test runs it but
	// nothing detects the mutation — theatre). That status split IS the
	// gap/theatre distinction; it requires coverage to be on (see README).
	const srcFile = (db.query("SELECT file FROM mutants LIMIT 1").get() as Row | null)?.file;

	// --- gaps: code no test even executes ---
	const gaps = db.query("SELECT line, mutator, count(*) n FROM mutants WHERE status='NoCoverage' GROUP BY line, mutator ORDER BY line").all() as Row[];
	const gapTotal = gaps.reduce((a, r) => a + (r.n as number), 0);
	p(`\nGAPS  (NoCoverage — no test executes this code: ${gapTotal})`);
	if (gapTotal === 0) p(`  none — every mutable location is reached by some test`);
	for (const r of gaps) p(`  ${srcFile}:${r.line}  ${r.mutator}${(r.n as number) > 1 ? ` ×${r.n}` : ""}`);

	// --- theatre: covered but survived ---
	const theatre = db.query("SELECT line, mutator, count(*) n FROM mutants WHERE status='Survived' GROUP BY line, mutator ORDER BY line").all() as Row[];
	const theatreTotal = theatre.reduce((a, r) => a + (r.n as number), 0);
	p(`\nTHEATRE  (Survived — code is covered but no test detects the mutation: ${theatreTotal})`);
	if (theatreTotal === 0) p(`  none`);
	for (const r of theatre) p(`  ${srcFile}:${r.line}  ${r.mutator}${(r.n as number) > 1 ? ` ×${r.n}` : ""}`);

	return out.join("\n");
}

if (import.meta.main) {
	const reportPath = process.argv[2] ?? "reports/mutation/mutation.json";
	const mreport = (await Bun.file(reportPath).json()) as MutationReport;
	const db = buildDb(mreport, "reports/test-debt.sqlite");
	console.log(report(db));
	db.close();
}
