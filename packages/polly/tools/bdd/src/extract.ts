/**
 * The verify cross-link, half one: reduce each scenario to a {@link ScenarioTrace}
 * over the *same vocabulary the verification config speaks* — Given (initial
 * state exprs) → When (message types) → Then (state exprs).
 *
 * This is to `.feature` files what `extractCondition` (tools/analysis) is to a
 * `requires()` call: it reads the statically-declared `message`/`stateExpr`
 * metadata off each matched step binding and hands check-verify a structure it
 * can compare against the config and the TLA+ model. Steps that match no
 * binding are kept as `unbound` so gaps are visible rather than silently empty.
 */
import { parseFeatureFile } from "./parse.ts";
import { matchStep, resetRegistry } from "./steps.ts";
import type { ScenarioTrace, TraceStep } from "./types.ts";

async function loadStepModules(stepFiles: string[]): Promise<void> {
  resetRegistry();
  for (const file of stepFiles) {
    await import(`${file}?t=${Bun.nanoseconds()}`);
  }
}

function toTraceStep(text: string, keyword: TraceStep["keyword"]): TraceStep {
  const match = matchStep(text, keyword);
  if (!match) return { text, keyword, unbound: true };
  return {
    text,
    keyword,
    message: match.binding.message,
    stateExpr: match.binding.stateExpr,
  };
}

export async function extractTraces(
  featureFiles: string[],
  stepFiles: string[]
): Promise<ScenarioTrace[]> {
  await loadStepModules(stepFiles);
  const traces: ScenarioTrace[] = [];

  for (const file of featureFiles) {
    const feature = await parseFeatureFile(file);
    for (const scenario of feature.scenarios) {
      const allSteps = [...feature.background, ...scenario.steps];
      const trace: ScenarioTrace = {
        feature: feature.name,
        scenario: scenario.name,
        tags: [...feature.tags, ...scenario.tags],
        given: [],
        when: [],
        // biome-ignore lint/suspicious/noThenProperty: `then` is Gherkin vocabulary here, not a thenable.
        then: [],
        file,
      };
      for (const step of allSteps) {
        trace[step.keyword].push(toTraceStep(step.text, step.keyword));
      }
      traces.push(trace);
    }
  }
  return traces;
}
