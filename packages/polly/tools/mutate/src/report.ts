/**
 * Test-debt report: derive the three signals from the kill matrix.
 *
 *   gaps        survived mutants — code no test pins (the Stryker direction)
 *   redundancy  tests/files whose every kill is also caught elsewhere
 *   theatre     covered-but-survived — code a test runs but no test detects
 *               (the Survived status under coverageAnalysis "all")
 *   contracts   (bun engine, contracts on) mutants only a requires/ensures
 *               caught, kills per contract, and contracts whose handler was
 *               exercised yet never fired — a contract without teeth
 *
 * Redundancy is reported at BOTH file and case level. Decisions are keyed at
 * file level (stable identity); case level is the drill-down.
 */
import type { Database } from "bun:sqlite";
import { buildDb, loadMutationReport, queryAll, queryGet } from "./ingest.ts";

type SubsumedCase = { file: string; name: string; total: number };
type LineCount = { file: string; line: number; mutator: string; n: number };
type SiteKills = {
  id: string;
  primitive: string;
  message: string | null;
  n: number;
  exercised: number;
};

/** Tests under which the unmutated code already fails a contract. */
function violationLines(db: Database, p: (s?: string) => void): void {
  const violations = queryAll<{ target: string; test: string; contract_id: string | null }>(
    db,
    "SELECT target, test, contract_id FROM contract_violations ORDER BY target, test, contract_id"
  );
  if (violations.length === 0) return;
  p(
    `  TEST VIOLATES CONTRACT  (the unmutated code fails a contract under a test: ${violations.length})`
  );
  for (const v of violations) {
    p(`    ${v.target}: ${v.test}${v.contract_id ? ` → ${v.contract_id}` : ""}`);
  }
}

/** Mutants only a contract killed, grouped by line and mutator. */
function contractOnlyLines(db: Database, p: (s?: string) => void): void {
  const only = queryAll<LineCount>(
    db,
    "SELECT file, line, mutator, count(*) n FROM mutants WHERE contract_only=1 GROUP BY file, line, mutator ORDER BY file, line"
  );
  const onlyTotal = only.reduce((a, r) => a + r.n, 0);
  p(`  CONTRACT-ONLY KILLS  (no test assertion caught these; a contract did: ${onlyTotal})`);
  for (const r of only) p(`    ${r.file}:${r.line}  ${r.mutator}${r.n > 1 ? ` ×${r.n}` : ""}`);
}

/** Kills per contract site, then the sites that never fired and why. */
function perContractLines(db: Database, p: (s?: string) => void): void {
  const sites = queryAll<SiteKills>(
    db,
    `SELECT s.id, s.primitive, s.message,
            (SELECT count(*) FROM contract_kills k WHERE k.contract_id = s.id) n,
            (SELECT count(*) FROM mutants m
              WHERE m.file = s.file AND s.handler_from IS NOT NULL
                AND m.line BETWEEN s.handler_from AND s.handler_to
                AND m.status IN ('Killed', 'Survived', 'Timeout')) exercised
     FROM contract_sites s ORDER BY n DESC, s.id`
  );
  p(`  KILLS PER CONTRACT`);
  for (const s of sites) {
    p(`    ${s.id}  ${s.primitive}  ${s.n} kill(s)${s.message ? `  “${s.message}”` : ""}`);
  }
  const toothless = sites.filter((s) => s.n === 0 && s.exercised > 0);
  const idle = sites.filter((s) => s.n === 0 && s.exercised === 0);
  p(
    `  CONTRACTS WITHOUT TEETH  (the handler's mutants ran, the contract never fired: ${toothless.length})`
  );
  if (toothless.length === 0) p(`    none`);
  for (const s of toothless) p(`    ${s.id}  ${s.primitive}${s.message ? `  “${s.message}”` : ""}`);
  if (idle.length > 0) {
    p(`  HANDLER NOT EXERCISED  (no mutant in the contract's handler ran: ${idle.length})`);
    for (const s of idle) p(`    ${s.id}  ${s.primitive}`);
  }
}

/** The CONTRACTS section; nothing when the report has no contracts block (Stryker-era). */
function contractsSection(db: Database, p: (s?: string) => void): void {
  const meta = new Map(
    queryAll<{ key: string; value: string }>(db, "SELECT key, value FROM report_meta").map((r) => [
      r.key,
      r.value,
    ])
  );
  const mode = meta.get("contracts_mode");
  if (mode === undefined) return;
  const nSites = queryGet<{ n: number }>(db, "SELECT count(*) n FROM contract_sites")?.n ?? 0;
  p(`\nCONTRACTS  (requires/ensures as kill oracles — mode ${mode}, ${nSites} site(s))`);
  if (mode === "off") {
    p(
      `  off — the sites are inventoried only; 'polly mutate run --contracts all' makes each one fail the test that falsifies it`
    );
    return;
  }
  violationLines(db, p);
  if (meta.get("runner") === "command") {
    p(
      `  command runner: no per-test results, so kills are not attributed to contracts; compare the killed count against a --contracts off run`
    );
    return;
  }
  if (mode === "ensures") p(`  requires sites are inventoried, not enforced (mode ensures)`);
  contractOnlyLines(db, p);
  if (nSites === 0) return;
  perContractLines(db, p);
}

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
    invalid: number;
    ignored: number;
  }>(
    db,
    "SELECT count(*) n, sum(status='Killed') killed, sum(status='Survived') survived, sum(status='Timeout') timeout, sum(status='NoCoverage') nocov, sum(status='CompileError') invalid, sum(status='Ignored') ignored FROM mutants"
  ) ?? { n: 0, killed: 0, survived: 0, timeout: 0, nocov: 0, invalid: 0, ignored: 0 };
  const nTests = queryGet<{ n: number }>(db, "SELECT count(*) n FROM tests")?.n ?? 0;
  // Stryker's score, the same one `run` prints: detected / (detected +
  // undetected). CompileError, Ignored and RuntimeError mutants are not in it.
  const detected = tot.killed + tot.timeout;
  const valid = detected + tot.survived + tot.nocov;
  const score = valid === 0 ? "n/a" : `${((detected / valid) * 100).toFixed(1)}%`;
  const excluded = [
    tot.invalid > 0 ? `${tot.invalid} invalid` : "",
    tot.ignored > 0 ? `${tot.ignored} ignored` : "",
  ]
    .filter(Boolean)
    .map((s) => ` · ${s}`)
    .join("");
  p(
    `MUTATION  score ${score}   ${tot.killed} killed · ${tot.timeout} timeout · ${tot.survived} survived · ${tot.nocov} no-coverage${excluded}   (${tot.n} mutants, ${nTests} tests)`
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
    p(`  cannot be derived. Run 'polly mutate run --mode matrix' (every`);
    p(
      `  killer recorded), or 'polly mutate verify' to diagnose. Score/gaps/theatre below still hold.`
    );
  }

  // A non-killed mutant is NoCoverage (no test reaches it — a true gap) or
  // Survived (a test reaches it but nothing detects the mutation — theatre).
  // That status split IS the gap/theatre distinction (see README).
  // Each line names its own file: a run holds many targets.
  const byLine = (status: string) =>
    queryAll<LineCount>(
      db,
      `SELECT file, line, mutator, count(*) n FROM mutants WHERE status='${status}' GROUP BY file, line, mutator ORDER BY file, line`
    );
  const lineOf = (r: LineCount) =>
    `  ${r.file}:${r.line}  ${r.mutator}${r.n > 1 ? ` ×${r.n}` : ""}`;

  // --- gaps: code no test even executes ---
  const gaps = byLine("NoCoverage");
  const gapTotal = gaps.reduce((a, r) => a + r.n, 0);
  p(`\nGAPS  (NoCoverage — no test executes this code: ${gapTotal})`);
  if (gapTotal === 0) p(`  none — every mutable location is reached by some test`);
  for (const r of gaps) p(lineOf(r));

  // --- theatre: covered but survived ---
  const theatre = byLine("Survived");
  const theatreTotal = theatre.reduce((a, r) => a + r.n, 0);
  p(`\nTHEATRE  (Survived — code is covered but no test detects the mutation: ${theatreTotal})`);
  if (theatreTotal === 0) p(`  none`);
  for (const r of theatre) p(lineOf(r));

  contractsSection(db, p);

  return out.join("\n");
}

if (import.meta.main) {
  const reportPath = process.argv[2] ?? "reports/mutation/mutation.json";
  const db = buildDb(await loadMutationReport(reportPath), "reports/test-debt.sqlite");
  console.log(report(db));
  db.close();
}
