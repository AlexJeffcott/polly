/**
 * Ingest a mutation report (mutation-testing-report-schema) into a
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
  /** Written by the bun engine; absent from Stryker-era reports. */
  contracts?: ReportContracts;
}
interface Mutant {
  id: string;
  mutatorName: string;
  status: string;
  location: { start: { line: number; column: number } };
  killedBy?: string[];
  coveredBy?: string[];
  /** Contract ids (`<file>:<line>`) a killing test's failure named. */
  killedByContract?: string[];
  /** Every killer failed through a contract: no assertion caught the mutant. */
  contractOnly?: boolean;
}

/** The engine's contracts block: how the run enforced requires/ensures, and what it found. */
export interface ReportContracts {
  mode: "off" | "ensures" | "all";
  runner: "bun-test" | "command";
  sites: ContractSiteDef[];
  violations: { target: string; test: string; contracts: string[] }[];
}
export interface ContractSiteDef {
  /** `<file>:<line>`, what `killedByContract` holds. */
  id: string;
  file: string;
  line: number;
  primitive: "requires" | "ensures";
  message?: string;
  handler?: { from: number; to: number };
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
		DROP TABLE IF EXISTS contract_kills;
		DROP TABLE IF EXISTS contract_sites;
		DROP TABLE IF EXISTS contract_violations;
		DROP TABLE IF EXISTS report_meta;
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
			status TEXT NOT NULL,
			contract_only INTEGER NOT NULL DEFAULT 0
		);
		-- requires/ensures sites and the mutants each one killed (bun engine, contracts on)
		CREATE TABLE contract_sites (
			id TEXT PRIMARY KEY,
			file TEXT NOT NULL,
			line INTEGER NOT NULL,
			primitive TEXT NOT NULL,
			message TEXT,
			handler_from INTEGER,
			handler_to INTEGER
		);
		CREATE TABLE contract_kills (
			mutant_id TEXT NOT NULL REFERENCES mutants(id),
			contract_id TEXT NOT NULL,
			PRIMARY KEY (mutant_id, contract_id)
		);
		CREATE TABLE contract_violations (
			target TEXT NOT NULL,
			test TEXT NOT NULL,
			contract_id TEXT
		);
		CREATE TABLE report_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
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
    "INSERT INTO mutants (id, mutator, file, line, status, contract_only) VALUES (?, ?, ?, ?, ?, ?)"
  );
  const insKill = db.prepare("INSERT OR IGNORE INTO kills (mutant_id, test_id) VALUES (?, ?)");
  const insCover = db.prepare("INSERT OR IGNORE INTO covers (mutant_id, test_id) VALUES (?, ?)");
  const insContractKill = db.prepare(
    "INSERT OR IGNORE INTO contract_kills (mutant_id, contract_id) VALUES (?, ?)"
  );
  const insSite = db.prepare(
    "INSERT OR IGNORE INTO contract_sites (id, file, line, primitive, message, handler_from, handler_to) VALUES (?, ?, ?, ?, ?, ?, ?)"
  );
  const insViolation = db.prepare(
    "INSERT INTO contract_violations (target, test, contract_id) VALUES (?, ?, ?)"
  );
  const insMeta = db.prepare("INSERT INTO report_meta (key, value) VALUES (?, ?)");

  // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: two flat insert loops inside one transaction — keeping them together is the point.
  const ingest = db.transaction(() => {
    for (const [file, tf] of Object.entries(report.testFiles ?? {})) {
      for (const t of tf.tests) {
        insTest.run(t.id, file || "(unknown)", t.name, t.location?.start.line ?? null);
      }
    }
    for (const [file, f] of Object.entries(report.files)) {
      for (const m of f.mutants) {
        insMut.run(
          m.id,
          m.mutatorName,
          file,
          m.location.start.line,
          m.status,
          m.contractOnly ? 1 : 0
        );
        for (const tid of m.killedBy ?? []) insKill.run(m.id, tid);
        for (const tid of m.coveredBy ?? []) insCover.run(m.id, tid);
        for (const cid of m.killedByContract ?? []) insContractKill.run(m.id, cid);
      }
    }
    const contracts = report.contracts;
    if (contracts) {
      insMeta.run("contracts_mode", contracts.mode);
      insMeta.run("runner", contracts.runner);
      for (const s of contracts.sites) {
        insSite.run(
          s.id,
          s.file,
          s.line,
          s.primitive,
          s.message ?? null,
          s.handler?.from ?? null,
          s.handler?.to ?? null
        );
      }
      for (const v of contracts.violations) {
        if (v.contracts.length === 0) insViolation.run(v.target, v.test, null);
        for (const cid of v.contracts) insViolation.run(v.target, v.test, cid);
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
