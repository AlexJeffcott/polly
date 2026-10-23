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
import { isRecord, readNumber, readString, readStringArray } from "../../../src/shared/lib/guards";

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

/**
 * One SQL result row, read field by field. Each reader returns the field when
 * it has the named type and throws otherwise, naming the query and the field,
 * so a schema drift between `buildDb` and a reader fails where it is read.
 */
export interface SqlRow {
  string(field: string): string;
  number(field: string): number;
  stringOrNull(field: string): string | null;
}

/** Builds a row's value from its fields; the row type is what this returns. */
export type RowParser<T> = (row: SqlRow) => T;

function sqlRow(sql: string, index: number, row: unknown): SqlRow {
  const where = `query "${sql.replace(/\s+/g, " ").trim()}" row ${index}`;
  if (!isRecord(row)) throw new Error(`${where} is not a record`);
  const fail = (field: string, kind: string): never => {
    const got = field in row ? JSON.stringify(row[field]) : "missing";
    throw new Error(`${where}: field "${field}" is not ${kind} (got ${got})`);
  };
  return {
    string: (field) => readString(row[field]) ?? fail(field, "a string"),
    number: (field) => readNumber(row[field]) ?? fail(field, "a number"),
    stringOrNull: (field) =>
      row[field] === null ? null : (readString(row[field]) ?? fail(field, "a string or null")),
  };
}

// SQL rows arrive untyped: bun:sqlite returns `unknown` rows when the
// statement is given no type argument, and each caller's parser checks them.
export function queryAll<T>(db: Database, sql: string, parse: RowParser<T>): T[] {
  const rows: unknown[] = db.query(sql).all();
  return rows.map((row, i) => parse(sqlRow(sql, i, row)));
}
export function queryGet<T>(db: Database, sql: string, parse: RowParser<T>): T | null {
  const row: unknown = db.query(sql).get();
  return row === null ? null : parse(sqlRow(sql, 0, row));
}

function isPosition(v: unknown): boolean {
  return isRecord(v) && typeof v["line"] === "number" && typeof v["column"] === "number";
}

function isOptionalStringArray(v: unknown): boolean {
  return v === undefined || readStringArray(v) !== undefined;
}

function isMutant(v: unknown): v is Mutant {
  return (
    isRecord(v) &&
    typeof v["id"] === "string" &&
    typeof v["mutatorName"] === "string" &&
    typeof v["status"] === "string" &&
    isRecord(v["location"]) &&
    isPosition(v["location"]["start"]) &&
    isOptionalStringArray(v["killedBy"]) &&
    isOptionalStringArray(v["coveredBy"]) &&
    isOptionalStringArray(v["killedByContract"]) &&
    (v["contractOnly"] === undefined || typeof v["contractOnly"] === "boolean")
  );
}

function isTestDef(v: unknown): v is TestDef {
  return (
    isRecord(v) &&
    typeof v["id"] === "string" &&
    typeof v["name"] === "string" &&
    (v["location"] === undefined || (isRecord(v["location"]) && isPosition(v["location"]["start"])))
  );
}

function isContractSite(v: unknown): v is ContractSiteDef {
  if (!isRecord(v)) return false;
  const handler = v["handler"];
  return (
    typeof v["id"] === "string" &&
    typeof v["file"] === "string" &&
    typeof v["line"] === "number" &&
    (v["primitive"] === "requires" || v["primitive"] === "ensures") &&
    (v["message"] === undefined || typeof v["message"] === "string") &&
    (handler === undefined ||
      (isRecord(handler) &&
        typeof handler["from"] === "number" &&
        typeof handler["to"] === "number"))
  );
}

function isViolation(v: unknown): v is ReportContracts["violations"][number] {
  return (
    isRecord(v) &&
    typeof v["target"] === "string" &&
    typeof v["test"] === "string" &&
    readStringArray(v["contracts"]) !== undefined
  );
}

function isContracts(v: unknown): v is ReportContracts {
  return (
    isRecord(v) &&
    (v["mode"] === "off" || v["mode"] === "ensures" || v["mode"] === "all") &&
    (v["runner"] === "bun-test" || v["runner"] === "command") &&
    Array.isArray(v["sites"]) &&
    v["sites"].every(isContractSite) &&
    Array.isArray(v["violations"]) &&
    v["violations"].every(isViolation)
  );
}

function everyEntry(v: unknown, key: string, item: (x: unknown) => boolean): boolean {
  if (!isRecord(v)) return false;
  return Object.values(v).every((entry) => {
    if (!isRecord(entry)) return false;
    const list = entry[key];
    return Array.isArray(list) && list.every(item);
  });
}

/**
 * The shape `buildDb` reads, checked in full. Fields outside it (Stryker's
 * `replacement`, `location.end`, `thresholds`, …) are allowed and kept.
 */
export function isMutationReport(v: unknown): v is MutationReport {
  return (
    isRecord(v) &&
    typeof v["schemaVersion"] === "string" &&
    everyEntry(v["files"], "mutants", isMutant) &&
    (v["testFiles"] === undefined || everyEntry(v["testFiles"], "tests", isTestDef)) &&
    (v["contracts"] === undefined || isContracts(v["contracts"]))
  );
}

export async function loadMutationReport(path: string): Promise<MutationReport> {
  const parsed: unknown = await Bun.file(path).json();
  if (!isMutationReport(parsed)) {
    throw new Error(`${path} is not a mutation report (mutation-testing-report-schema)`);
  }
  return parsed;
}

if (import.meta.main) {
  const reportPath = process.argv[2] ?? "reports/mutation/mutation.json";
  const dbPath = process.argv[3] ?? "reports/test-debt.sqlite";
  const db = buildDb(await loadMutationReport(reportPath), dbPath);
  const n = queryGet(
    db,
    "SELECT (SELECT count(*) FROM tests) t, (SELECT count(*) FROM mutants) m, (SELECT count(*) FROM kills) k",
    (r) => ({ t: r.number("t"), m: r.number("m"), k: r.number("k") })
  ) ?? { t: 0, m: 0, k: 0 };
  console.log(`Ingested ${reportPath} -> ${dbPath}`);
  console.log(`  ${n.t} tests, ${n.m} mutants, ${n.k} kill-edges`);
  db.close();
}
