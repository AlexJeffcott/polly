/**
 * Ingest a Stryker mutation report (mutation-testing-report-schema) into a
 * regenerable SQLite database holding the kill matrix.
 *
 * The tool consumes the *schema*, never a specific runner — so the same
 * analysis works whether the matrix came from the patched bun runner, the
 * tap runner, or an eventual official Bun plugin. The db is a build artefact
 * (gitignored); decisions are kept elsewhere in version control.
 */
import { Database } from "bun:sqlite";

export interface MutationReport {
  schemaVersion: string;
  files: Record<string, { mutants: Mutant[] }>;
  testFiles?: Record<string, { tests: TestDef[] }>;
}
interface Mutant {
  id: string;
  mutatorName: string;
  status: string;
  location: { start: { line: number; column: number } };
  killedBy?: string[];
  coveredBy?: string[];
}
interface TestDef {
  id: string;
  name: string;
  location?: { start: { line: number; column: number } };
}

export function buildDb(report: MutationReport, dbPath = ":memory:"): Database {
  const db = new Database(dbPath);
  db.exec("PRAGMA journal_mode = WAL;");
  db.exec(`
		DROP TABLE IF EXISTS kills;
		DROP TABLE IF EXISTS covers;
		DROP TABLE IF EXISTS mutants;
		DROP TABLE IF EXISTS tests;
		CREATE TABLE tests (
			id TEXT PRIMARY KEY,
			file TEXT NOT NULL,
			name TEXT NOT NULL,
			line INTEGER
		);
		CREATE TABLE mutants (
			id TEXT PRIMARY KEY,
			mutator TEXT NOT NULL,
			file TEXT NOT NULL,
			line INTEGER,
			status TEXT NOT NULL
		);
		-- the kill matrix: (mutant, test) where test detects mutant
		CREATE TABLE kills (
			mutant_id TEXT NOT NULL REFERENCES mutants(id),
			test_id TEXT NOT NULL REFERENCES tests(id),
			PRIMARY KEY (mutant_id, test_id)
		);
		-- coverage matrix (populated only when the runner reports coveredBy)
		CREATE TABLE covers (
			mutant_id TEXT NOT NULL REFERENCES mutants(id),
			test_id TEXT NOT NULL REFERENCES tests(id),
			PRIMARY KEY (mutant_id, test_id)
		);
		CREATE INDEX idx_kills_test ON kills(test_id);
		CREATE INDEX idx_kills_mutant ON kills(mutant_id);
	`);

  const insTest = db.prepare(
    "INSERT OR IGNORE INTO tests (id, file, name, line) VALUES (?, ?, ?, ?)"
  );
  const insMut = db.prepare(
    "INSERT INTO mutants (id, mutator, file, line, status) VALUES (?, ?, ?, ?, ?)"
  );
  const insKill = db.prepare("INSERT OR IGNORE INTO kills (mutant_id, test_id) VALUES (?, ?)");
  const insCover = db.prepare("INSERT OR IGNORE INTO covers (mutant_id, test_id) VALUES (?, ?)");

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: two flat insert loops inside one transaction — keeping them together is the point.
  const ingest = db.transaction(() => {
    for (const [file, tf] of Object.entries(report.testFiles ?? {})) {
      for (const t of tf.tests) {
        insTest.run(t.id, file || "(unknown)", t.name, t.location?.start.line ?? null);
      }
    }
    for (const [file, f] of Object.entries(report.files)) {
      for (const m of f.mutants) {
        insMut.run(m.id, m.mutatorName, file, m.location.start.line, m.status);
        for (const tid of m.killedBy ?? []) insKill.run(m.id, tid);
        for (const tid of m.coveredBy ?? []) insCover.run(m.id, tid);
      }
    }
  });
  ingest();
  return db;
}

// SQL rows and the on-disk report arrive untyped; these three helpers are the
// single sanctioned cast boundary (the `as unknown as` escape hatch) so call
// sites stay assertion-free and the column/shape types live next to the query.
export function queryAll<T>(db: Database, sql: string): T[] {
  return db.query(sql).all() as unknown as T[];
}
export function queryGet<T>(db: Database, sql: string): T | null {
  return db.query(sql).get() as unknown as T | null;
}
export async function loadMutationReport(path: string): Promise<MutationReport> {
  return (await Bun.file(path).json()) as unknown as MutationReport;
}

if (import.meta.main) {
  const reportPath = process.argv[2] ?? "reports/mutation/mutation.json";
  const dbPath = process.argv[3] ?? "reports/test-debt.sqlite";
  const db = buildDb(await loadMutationReport(reportPath), dbPath);
  const n = queryGet<{ t: number; m: number; k: number }>(
    db,
    "SELECT (SELECT count(*) FROM tests) t, (SELECT count(*) FROM mutants) m, (SELECT count(*) FROM kills) k"
  ) ?? { t: 0, m: 0, k: 0 };
  console.log(`Ingested ${reportPath} -> ${dbPath}`);
  console.log(`  ${n.t} tests, ${n.m} mutants, ${n.k} kill-edges`);
  db.close();
}
