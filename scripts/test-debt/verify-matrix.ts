/**
 * Verification artefact for the kill-matrix contract.
 *
 * The whole test-debt tool rests on one fact: the patched bun runner emits a
 * COMPLETE kill matrix — every test that detects a mutant appears in killedBy,
 * not just the first. That depends on a pinned pair: (Bun version, plugin
 * version + our patch). A Bun upgrade that changes JUnit output, or a patch
 * that stops applying, would silently collapse killedBy to one id each — a
 * green board with the redundancy signal quietly dead (the classic trap).
 *
 * This runs a real mutation pass and asserts the contract. One command,
 * "success" or a specific failure. Run it after any bump of Bun or the plugin.
 *
 *   bun scripts/test-debt/verify-matrix.ts          # uses existing report
 *   bun scripts/test-debt/verify-matrix.ts --run    # runs stryker first
 */
import type { MutationReport } from "./ingest.ts";

const REPORT = "reports/mutation/mutation.json";

if (process.argv.includes("--run")) {
	console.log("Running mutation pass (this takes ~45min for the 13-module Polly primitive set)...");
	const proc = Bun.spawn(["bunx", "stryker", "run"], { stdout: "inherit", stderr: "inherit" });
	const code = await proc.exited;
	if (code !== 0) fail(`stryker run exited ${code}`);
}

if (!(await Bun.file(REPORT).exists())) {
	fail(`no report at ${REPORT}. Run with --run, or 'bun run mutation' first.`);
}

const report = (await Bun.file(REPORT).json()) as MutationReport;
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
	`${realPaths.length} file(s): ${realPaths.slice(0, 2).join(", ")}${realPaths.length > 2 ? "…" : ""}`,
);

// 3. test ids resolve
const testIds = new Set(Object.values(report.testFiles ?? {}).flatMap((tf) => tf.tests.map((t) => t.id)));
const mutants = Object.values(report.files).flatMap((f) => f.mutants);
const killed = mutants.filter((m) => m.status === "Killed");
const danglingKb = killed.filter((m) => (m.killedBy ?? []).some((id) => !testIds.has(id)));
add("every killedBy id resolves to a test", danglingKb.length === 0, `${danglingKb.length} dangling`);

// 4. THE contract: a complete matrix means some killed mutant has >1 killer.
//    If bail silently re-engaged, every killedBy would have length 1.
const withKb = killed.filter((m) => (m.killedBy ?? []).length > 0);
const multi = killed.filter((m) => (m.killedBy ?? []).length > 1);
add("killed mutants carry killedBy", killed.length > 0 && withKb.length === killed.length, `${withKb.length}/${killed.length}`);
add(
	"matrix is complete (no-bail): >1 killer exists",
	multi.length > 0,
	`${multi.length} mutant(s) killed by >1 test — collapses to 0 if bail re-engages`,
);

// 5. coverage extraction works: if the afterAll dump fails, the coverage map is
//    empty and Stryker marks EVERY mutant NoCoverage (theatre/gap split dies).
const noCov = mutants.filter((m) => m.status === "NoCoverage").length;
add("coverage collected (not all NoCoverage)", noCov < mutants.length, `${noCov}/${mutants.length} NoCoverage — all-NoCoverage means the coverage dump broke`);

// report
let allOk = true;
console.log("\nKill-matrix contract:");
for (const c of checks) {
	console.log(`  ${c.ok ? "✓" : "✗"} ${c.name}  (${c.detail})`);
	if (!c.ok) allOk = false;
}
if (!allOk) {
	console.error("\n✗ Contract broken. The pinned pair has drifted — re-check Bun version and that the patch applies (bun install).");
	process.exit(1);
}
console.log("\n✓ Kill-matrix contract holds.");

function fail(msg: string): never {
	console.error(`✗ ${msg}`);
	process.exit(1);
}
