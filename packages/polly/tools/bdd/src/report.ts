/**
 * Human- and machine-readable formatting of a {@link RunResult}.
 */
import type { RunResult, ScenarioResult } from "./types.ts";

const MARK: Record<ScenarioResult["outcome"], string> = {
  pass: "✓",
  fail: "✗",
  undefined: "?",
  "deferred-formal": "→",
};

function relFile(file: string, cwd: string): string {
  return file.startsWith(cwd) ? file.slice(cwd.length + 1) : file;
}

/** The detail lines under a failed/undefined/deferred scenario. */
function scenarioDetail(s: ScenarioResult): string[] {
  if (s.outcome === "deferred-formal") {
    return [
      "      deferred to polly verify — precondition is formal-only (requires() is a runtime no-op)",
    ];
  }
  if (s.outcome !== "fail" && s.outcome !== "undefined") return [];
  const lines: string[] = [];
  for (const step of s.steps) {
    if (step.outcome !== "fail" && step.outcome !== "undefined") continue;
    lines.push(`      ${step.outcome === "fail" ? "✗" : "?"} ${step.rawKeyword} ${step.text}`);
    if (step.message) lines.push(`        ↳ ${step.message}`);
  }
  return lines;
}

export function formatRun(result: RunResult, cwd: string): string {
  const lines: string[] = [];
  let currentFeature = "";

  for (const s of result.scenarios) {
    if (s.feature !== currentFeature) {
      currentFeature = s.feature;
      lines.push(`\nFeature: ${s.feature}  (${relFile(s.file, cwd)})`);
    }
    lines.push(`  ${MARK[s.outcome]} ${s.scenario}`);
    lines.push(...scenarioDetail(s));
  }

  lines.push("");
  lines.push(
    `${result.ok ? "✓" : "✗"} ${result.passed} passed, ${result.failed} failed, ` +
      `${result.undefinedSteps} undefined, ${result.deferred} deferred (formal)`
  );
  return lines.join("\n");
}

export function toJson(result: RunResult): string {
  return JSON.stringify(result, null, 2);
}
