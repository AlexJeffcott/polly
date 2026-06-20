/**
 * The runtime engine: parse features, load step modules, drive each scenario
 * against the *real* factory world the consumer built in `defineWorld`.
 *
 * What this stratum can and cannot check is deliberate. Runtime BDD asserts on
 * *observable* behaviour — state-signal changes and the response a handler
 * returns. Polly's `requires()` preconditions are runtime no-ops (they exist
 * only for the TLA+ model), so a precondition-only negative (e.g. "a guest
 * login is rejected") is NOT runtime-observable. Tag those `@formal`: the
 * runner defers them with a clear note, and `polly verify` is where they're
 * actually checked — the `requires()` guard is extracted into the TLA+ model.
 * This is the three strata dividing the work.
 */
import { parseFeatureFile } from "./parse.ts";
import { getWorldDef, matchStep, resetRegistry } from "./steps.ts";
import type {
  ParsedFeature,
  ParsedScenario,
  ParsedStep,
  RunResult,
  ScenarioResult,
  StepResult,
  World,
} from "./types.ts";

// Tags whose scenarios are formal-only — checked by `polly verify`, not the
// runtime runner. `@formal` covers precondition-only negatives (requires() is a
// runtime no-op); `@forbidden` covers safety claims ("this state never happens"),
// which a single runtime execution cannot establish. Both are deferred here and
// settled by `polly verify --witness`.
const DEFERRED_TAGS = new Set(["formal", "forbidden"]);

export interface RunOptions {
  featureFiles: string[];
  stepFiles: string[];
  /** Only run scenarios carrying this tag (without leading @); ~tag negates. */
  tagFilter?: string;
}

/** Import each step module so its `defineStep`/`defineWorld` side effects run. */
async function loadStepModules(stepFiles: string[]): Promise<void> {
  resetRegistry();
  for (const file of stepFiles) {
    // Cache-bust so repeated in-process runs re-register cleanly.
    await import(`${file}?t=${Bun.nanoseconds()}`);
  }
}

function tagMatches(tags: string[], filter?: string): boolean {
  if (!filter) return true;
  if (filter.startsWith("~")) return !tags.includes(filter.slice(1));
  return tags.includes(filter);
}

async function runStep(world: World, step: ParsedStep): Promise<StepResult> {
  const base = { text: step.text, rawKeyword: step.rawKeyword };
  const match = matchStep(step.text, step.keyword);
  if (!match) {
    return { ...base, outcome: "undefined", message: `no binding matches "${step.text}"` };
  }
  const fn = match.binding[step.keyword];
  if (!fn) {
    return {
      ...base,
      outcome: "undefined",
      message: `binding for "${step.text}" has no '${step.keyword}' callback`,
    };
  }
  try {
    const ret = await fn(world, ...match.args);
    // A `when` that returns the send promise gets its response captured.
    if (ret !== undefined) world.lastResponse = ret;
    return { ...base, outcome: "pass" };
  } catch (err) {
    world.lastError = err;
    return { ...base, outcome: "fail", message: err instanceof Error ? err.message : String(err) };
  }
}

async function runScenario(
  world: World,
  feature: ParsedFeature,
  scenario: ParsedScenario,
  reset: (w: World) => void | Promise<void>
): Promise<ScenarioResult> {
  const result: ScenarioResult = {
    feature: feature.name,
    scenario: scenario.name,
    tags: scenario.tags,
    outcome: "pass",
    steps: [],
    file: feature.file,
  };

  // Cold start: reset the world (signals → initial) and clear per-scenario scratch.
  await reset(world);
  world.vars = {};
  world.lastResponse = undefined;
  world.lastError = undefined;

  const steps = [...feature.background, ...scenario.steps];
  let aborted = false;
  for (const step of steps) {
    if (aborted) {
      result.steps.push({ text: step.text, rawKeyword: step.rawKeyword, outcome: "skipped" });
      continue;
    }
    const sr = await runStep(world, step);
    result.steps.push(sr);
    if (sr.outcome === "fail") {
      result.outcome = "fail";
      aborted = true;
    } else if (sr.outcome === "undefined") {
      result.outcome = result.outcome === "fail" ? "fail" : "undefined";
      aborted = true;
    }
  }
  return result;
}

export async function runFeatures(options: RunOptions): Promise<RunResult> {
  await loadStepModules(options.stepFiles);

  const worldDef = getWorldDef();
  if (!worldDef) {
    throw new Error(
      "no world defined. A step module must call defineWorld({ create, reset }) — see tools/bdd/README.md."
    );
  }
  const world = await worldDef.create();

  const features = await Promise.all(options.featureFiles.map((f) => parseFeatureFile(f)));
  const scenarios: ScenarioResult[] = [];

  try {
    for (const feature of features) {
      for (const scenario of feature.scenarios) {
        const tags = [...feature.tags, ...scenario.tags];
        if (!tagMatches(tags, options.tagFilter)) continue;

        if (tags.some((t) => DEFERRED_TAGS.has(t))) {
          scenarios.push({
            feature: feature.name,
            scenario: scenario.name,
            tags,
            outcome: "deferred-formal",
            steps: [],
            file: feature.file,
          });
          continue;
        }
        scenarios.push(await runScenario(world, feature, { ...scenario, tags }, worldDef.reset));
      }
    }
  } finally {
    // Release any real resources the world holds (browsers, relay, sockets),
    // even when a scenario threw — otherwise the runner hangs on live handles.
    await worldDef.teardown?.(world);
  }

  const passed = scenarios.filter((s) => s.outcome === "pass").length;
  const failed = scenarios.filter((s) => s.outcome === "fail").length;
  const undef = scenarios.filter((s) => s.outcome === "undefined").length;
  const deferred = scenarios.filter((s) => s.outcome === "deferred-formal").length;

  return {
    scenarios,
    passed,
    failed,
    undefinedSteps: undef,
    deferred,
    ok: failed === 0 && undef === 0,
  };
}
