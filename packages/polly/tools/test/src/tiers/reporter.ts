/**
 * Reporting for engine runs: a human summary table (with per-case timing and a
 * slowest-N list, the data the old `&&` chains never captured) and a JSON
 * artefact for tooling. No cloud reporters — everything lands on disk locally.
 */
import type { RunReport, TierPlan } from "./types";

const ICON = { pass: "✓", fail: "✗", skip: "⊘", timeout: "⏱" } as const;

/** One-line-per-case summary plus totals and slowest cases. */
export function formatSummary(report: RunReport): string {
  const lines: string[] = [];
  lines.push("");
  lines.push("── results ─────────────────────────────────");
  for (const c of report.cases) {
    const time = c.outcome === "skip" ? "" : `${c.durationMs}ms`;
    const tail = c.outcome === "skip" ? ` (${c.skipReason})` : c.message ? ` — ${c.message}` : "";
    lines.push(`${ICON[c.outcome]} ${c.tier} › ${c.label}  ${time}${tail}`);
  }

  const ran = report.cases.filter((c) => c.outcome !== "skip");
  const slowest = [...ran].sort((a, b) => b.durationMs - a.durationMs).slice(0, 5);
  if (slowest.length > 0) {
    lines.push("");
    lines.push("slowest:");
    for (const c of slowest) lines.push(`  ${c.durationMs}ms  ${c.tier} › ${c.label}`);
  }

  lines.push("");
  lines.push(
    `${report.ok ? "PASS" : "FAIL"}  ${report.passed} passed, ${report.failed} failed, ` +
      `${report.skipped} skipped in ${(report.durationMs / 1000).toFixed(1)}s`
  );
  return lines.join("\n");
}

/** Stable JSON artefact written to test-results/. */
export function toJSON(report: RunReport): string {
  return JSON.stringify(report, null, 2);
}

/** `--list` output: tiers and their cases without running anything. */
export function formatPlan(plan: TierPlan): string {
  const lines: string[] = ["Tiers (run order):", ""];
  for (const tier of plan.tiers) {
    const conc = tier.concurrency && tier.concurrency > 1 ? ` ×${tier.concurrency}` : "";
    lines.push(`${tier.name}${conc}${tier.description ? ` — ${tier.description}` : ""}`);
    for (const c of tier.cases) {
      const needs = c.needs && c.needs.length > 0 ? `  (needs ${c.needs.join(", ")})` : "";
      lines.push(`    ${c.id}${needs}`);
    }
    lines.push("");
  }
  return lines.join("\n");
}
