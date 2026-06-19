/**
 * The deeper verify cross-link: reduce each scenario to its *Then-predicate* —
 * the observable post-state a passing scenario claims is reachable.
 *
 * Where {@link extractTraces} (and `polly bdd check`) ask "does this scenario
 * speak the config's vocabulary?", a witness asks the *formal* question: "can
 * the exhaustive model actually reach the state this scenario asserts?" A
 * scenario whose Then-state the model proves unreachable is a scenario that
 * lies — green in the runner, impossible in the model. `polly verify --witness`
 * turns each predicate produced here into a per-scenario TLC reachability check
 * (tools/verify); this module never runs a model checker — it only reduces.
 *
 * The reduction reuses the same dual-use `stateExpr` metadata the static check
 * reads, but it needs the *whole* predicate, not just the field names. So it
 * substitutes the values captured from the step text into the binding's
 * `stateExpr` placeholders: a `then` bound to `user.role === "{0}"` matched
 * against `their role is "admin"` reduces to `user.role === "admin"`. Then-steps
 * whose `stateExpr` is a bare field reference (no comparison) or absent (a
 * runtime-only assertion like `the change is refused`) are not state-observable
 * outcomes — they are reported as skipped, never silently dropped.
 */
import { parseFeatureFile } from "./parse.ts";
import { matchStep, resetRegistry } from "./steps.ts";

/** A scenario reduced to the post-state it claims, ready for the verify witness. */
export interface ScenarioWitness {
  feature: string;
  scenario: string;
  tags: string[];
  file: string;
  /**
   * The conjoined Then-predicate (TS, `signal.field` dialect, values
   * substituted) — e.g. `user.loggedIn === true && user.role === "admin"`.
   * `null` when the scenario has no state-observable outcome to witness.
   */
  predicate: string | null;
  /** Dotted state-field paths the predicate references (for subsystem routing). */
  fields: string[];
  /** Then-step texts skipped: a bare field ref, no binding, or a runtime-only check. */
  skipped: string[];
}

async function loadStepModules(stepFiles: string[]): Promise<void> {
  resetRegistry();
  for (const file of stepFiles) {
    await import(`${file}?t=${Bun.nanoseconds()}`);
  }
}

/** A predicate is witnessable only if it actually compares — a bare field cannot. */
const COMPARISON = /===|!==|==|!=|<=|>=|<|>/;

/** Substitute `{0}`, `{1}`, … in a stateExpr with the values captured from the step text. */
function substituteArgs(expr: string, args: string[]): string {
  return expr.replace(/\{(\d+)\}/g, (whole, index) => args[Number(index)] ?? whole);
}

/** Dotted identifier paths in an expression, minus string literals and keywords. */
function fieldsIn(expr: string): string[] {
  const noStrings = expr.replace(/"[^"]*"|'[^']*'/g, "");
  const ids = noStrings.match(/[a-zA-Z_$][\w$]*(?:\.[a-zA-Z_$][\w$]*)*/g) ?? [];
  const ignore = new Set(["true", "false", "null", "undefined", "length", "value"]);
  return (
    ids
      .filter((id) => !ignore.has(id) && Number.isNaN(Number(id)))
      // Drop a trailing `.length` so routing sees the underlying field (`todos`).
      .map((id) => id.replace(/\.length$/, ""))
  );
}

/**
 * Reduce one scenario's Then steps to a witness. Conjoins every Then whose
 * bound `stateExpr` resolves to a comparison; records the rest as skipped.
 */
function reduceScenario(
  feature: { name: string; tags: string[]; background: ParsedStepLike[]; file: string },
  scenario: { name: string; tags: string[]; steps: ParsedStepLike[] }
): ScenarioWitness {
  const thenSteps = [...feature.background, ...scenario.steps].filter((s) => s.keyword === "then");
  const conjuncts: string[] = [];
  const skipped: string[] = [];

  for (const step of thenSteps) {
    const match = matchStep(step.text, "then");
    const expr = match?.binding.stateExpr;
    if (!expr) {
      skipped.push(step.text);
      continue;
    }
    const resolved = substituteArgs(expr, match.args);
    if (!COMPARISON.test(resolved)) {
      // A bare field reference (`todos`, `user.role`) names a field but asserts
      // nothing checkable — useful to `polly bdd check`, not to a witness.
      skipped.push(step.text);
      continue;
    }
    conjuncts.push(resolved);
  }

  const predicate = conjuncts.length > 0 ? conjuncts.join(" && ") : null;
  const fields = [...new Set(conjuncts.flatMap(fieldsIn))];
  return {
    feature: feature.name,
    scenario: scenario.name,
    tags: [...feature.tags, ...scenario.tags],
    file: feature.file,
    predicate,
    fields,
    skipped,
  };
}

interface ParsedStepLike {
  keyword: "given" | "when" | "then";
  text: string;
}

/**
 * Reduce every scenario in the given feature files to a {@link ScenarioWitness}.
 * Step modules are loaded for their `defineStep` side effects (the same import
 * trick {@link extractTraces} uses) so `matchStep` can resolve each Then.
 */
export async function extractWitnesses(
  featureFiles: string[],
  stepFiles: string[]
): Promise<ScenarioWitness[]> {
  await loadStepModules(stepFiles);
  const witnesses: ScenarioWitness[] = [];
  for (const file of featureFiles) {
    const feature = await parseFeatureFile(file);
    for (const scenario of feature.scenarios) {
      witnesses.push(
        reduceScenario(
          {
            name: feature.name,
            tags: feature.tags,
            background: feature.background,
            file: feature.file,
          },
          scenario
        )
      );
    }
  }
  return witnesses;
}
