/**
 * Decisions log — the version-controlled human-judgement layer.
 *
 * The signals (kill matrix, subsumption) are derived and regenerable; they live
 * in the gitignored SQLite db. *Decisions* about them — "this subsumed file is a
 * legitimate set of input-class guards, keep it" — are precious, can't be
 * regenerated, and are committed here as JSONL (one record per line: mergeable,
 * diffable, append-only, last-write-wins per file).
 *
 * Identity is the test FILE (stable across describe restructuring; git tracks
 * renames). Each decision stores two freshness stamps:
 *   - hash:   a normalised content hash of the test file at decision time.
 *             Differs → the test changed since you judged it → re-review.
 *   - signal: the subsumption snapshot at decision time. Drifts (e.g. a test
 *             elsewhere was deleted, so this file's kills became unique) → the
 *             matrix around it changed → re-review.
 *
 * A decision is trusted only while BOTH still hold. That's what stops a "keep"
 * verdict from silently outliving the reason it was made.
 *
 *   bun scripts/test-debt/decisions.ts                          # status (the join)
 *   bun scripts/test-debt/decisions.ts decide <file> <verdict> "<rationale>"
 *
 * verdicts: keep | prune | rewrite | investigate
 */
import { Database } from "bun:sqlite";
import { createHash } from "node:crypto";
import { buildDb, type MutationReport } from "./ingest.ts";

const LOG = "scripts/test-debt/decisions.jsonl";
const REPORT = "reports/mutation/mutation.json";
const VERDICTS = ["keep", "prune", "rewrite", "investigate"];

interface FileSignal {
	kills: number;
	uniqueKills: number;
	subsumed: boolean;
}
interface Decision {
	file: string;
	verdict: string;
	rationale: string;
	signal: FileSignal;
	hash: string | null;
	decided: string;
}

/** Strip comments + collapse whitespace so formatting/comment edits don't trip the stamp.
 *  Heuristic (not a full parser): a false change only triggers a harmless re-review. */
function normalizeSource(src: string): string {
	return src
		.replace(/\/\*[\s\S]*?\*\//g, "")
		.replace(/(^|[^:])\/\/[^\n]*/g, "$1")
		.replace(/\s+/g, " ")
		.trim();
}
async function fileHash(file: string): Promise<string | null> {
	const f = Bun.file(file);
	if (!(await f.exists())) return null;
	return createHash("sha256").update(normalizeSource(await f.text())).digest("hex").slice(0, 16);
}

export function fileSignals(db: Database): Map<string, FileSignal> {
	const rows = db
		.query(`
			WITH file_kill AS (SELECT DISTINCT t.file file, k.mutant_id mid FROM kills k JOIN tests t ON t.id=k.test_id),
			     owner AS (SELECT mid, count(DISTINCT file) nf FROM file_kill GROUP BY mid)
			SELECT fk.file file, count(DISTINCT fk.mid) kills,
			       sum(CASE WHEN o.nf=1 THEN 1 ELSE 0 END) unique_kills
			FROM file_kill fk JOIN owner o ON o.mid=fk.mid GROUP BY fk.file`)
		.all() as { file: string; kills: number; unique_kills: number }[];
	const m = new Map<string, FileSignal>();
	for (const r of rows) m.set(r.file, { kills: r.kills, uniqueKills: r.unique_kills, subsumed: r.kills > 0 && r.unique_kills === 0 });
	return m;
}

async function loadDecisions(): Promise<Map<string, Decision>> {
	const m = new Map<string, Decision>();
	const f = Bun.file(LOG);
	if (!(await f.exists())) return m;
	for (const line of (await f.text()).split("\n")) {
		const t = line.trim();
		if (!t) continue;
		const d = JSON.parse(t) as Decision;
		m.set(d.file, d); // last write wins
	}
	return m;
}

/** Why a decision no longer applies, or null if it still holds. */
function staleReason(d: Decision, currentHash: string | null, current: FileSignal | undefined): string | null {
	if (!current) return "file no longer kills any mutant (renamed/deleted/refactored?)";
	if (d.hash !== currentHash) return "test file changed since the decision";
	if (d.signal.subsumed !== current.subsumed) return `subsumption flipped (${d.signal.subsumed} → ${current.subsumed})`;
	if (d.signal.uniqueKills > 0 !== (current.uniqueKills > 0)) return `unique-kill status changed (${d.signal.uniqueKills} → ${current.uniqueKills})`;
	return null;
}

async function status(db: Database) {
	const signals = fileSignals(db);
	const decisions = await loadDecisions();
	const needsReview: string[] = [];
	const stale: string[] = [];
	const settled: string[] = [];

	for (const [file, sig] of [...signals].sort((a, b) => b[1].kills - a[1].kills)) {
		const d = decisions.get(file);
		if (!d) {
			if (sig.subsumed) needsReview.push(`  ${file}  (${sig.kills} kills, 0 unique)`);
			continue;
		}
		const reason = staleReason(d, await fileHash(file), sig);
		if (reason) stale.push(`  ${file}  [${d.verdict}] — ${reason}`);
		else settled.push(`  ${file}  [${d.verdict}] ${d.rationale ? `— ${d.rationale}` : ""}`);
	}
	// decided files that have dropped out of the signal set entirely
	for (const [file, d] of decisions) {
		if (!signals.has(file)) stale.push(`  ${file}  [${d.verdict}] — file no longer in matrix`);
	}

	const out: string[] = [];
	out.push(`NEEDS REVIEW  (subsumed files with no decision — ${needsReview.length})`);
	out.push(needsReview.length ? needsReview.join("\n") : "  none");
	out.push(`\nSTALE  (decision's basis drifted — re-review — ${stale.length})`);
	out.push(stale.length ? stale.join("\n") : "  none");
	out.push(`\nSETTLED  (fresh decisions, suppressed from action list — ${settled.length})`);
	out.push(settled.length ? settled.join("\n") : "  none");
	console.log(out.join("\n"));
}

async function decide(file: string, verdict: string, rationale: string, db: Database) {
	if (!VERDICTS.includes(verdict)) {
		console.error(`✗ verdict must be one of: ${VERDICTS.join(", ")}`);
		process.exit(1);
	}
	const sig = fileSignals(db).get(file);
	if (!sig) {
		console.error(`✗ ${file} is not a test file that kills any mutant in the current matrix`);
		process.exit(1);
	}
	const decided = new Date().toISOString().slice(0, 10);
	const record: Decision = { file, verdict, rationale, signal: sig, hash: await fileHash(file), decided };
	await Bun.write(LOG, (await Bun.file(LOG).exists() ? await Bun.file(LOG).text() : "") + JSON.stringify(record) + "\n");
	console.log(`✓ recorded: ${file} [${verdict}]${rationale ? ` — ${rationale}` : ""}`);
}

if (import.meta.main) {
	const report = (await Bun.file(REPORT).json()) as MutationReport;
	const db = buildDb(report, "reports/test-debt.sqlite");
	const [cmd, ...rest] = process.argv.slice(2);
	if (cmd === "decide") {
		const [file, verdict, ...r] = rest;
		await decide(file, verdict, r.join(" ").replace(/^"|"$/g, ""), db);
	} else {
		await status(db);
	}
	db.close();
}
