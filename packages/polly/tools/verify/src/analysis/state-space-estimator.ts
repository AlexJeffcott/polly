import {
  type ContextSetInput,
  generatedTabCount,
  hasDeclaredContexts,
  resolveContexts,
  sendBranchingFactor,
  type TabSetInput,
  targetSetCount,
} from "../codegen/model-constants";
import type {
  AdapterVerificationConfig,
  LegacyVerificationConfig,
  UnifiedVerificationConfig,
} from "../config/types";
import { isAdapterConfig, isLegacyConfig } from "../config/types";
import type { CodebaseAnalysis } from "../core/model";

export type FieldEstimate = {
  name: string;
  cardinality: number | "unbounded";
  kind: string;
};

export type StateSpaceEstimate = {
  /** Subsystem this estimate is for; absent for the monolithic model. */
  subsystem?: string;
  fields: FieldEstimate[];
  fieldProduct: number;
  handlerCount: number;
  maxInFlight: number;
  contextCount: number;
  /** The `Contexts` set the `.cfg` writer will emit, in emission order. */
  contexts: string[];
  /** Whether that set came from `config.contexts` or from the default (polly#185). */
  contextsDeclared: boolean;
  tabCount: number;
  /** `|Contexts| * (2^|Contexts| - 1) * |Tabs| * handlers` — one send's successors. */
  sendBranching: number;
  /** `fieldProduct ** contextCount` — application state, replicated per context. */
  totalStateSpace: number;
  /** `sendBranching ** maxInFlight` — the message configurations reachable. */
  interleavingFactor: number;
  estimatedStates: number;
  feasibility: "trivial" | "feasible" | "slow" | "infeasible";
  warnings: string[];
  suggestions: string[];
};

function typedFieldCardinality(name: string, obj: Record<string, unknown>): FieldEstimate | null {
  if (!("type" in obj)) return null;

  const values = obj["values"];
  const min = obj["min"];
  const max = obj["max"];

  switch (obj["type"]) {
    case "boolean":
      return { name, cardinality: 2, kind: "boolean" };
    case "enum":
      if (Array.isArray(values)) {
        return { name, cardinality: values.length, kind: "enum" };
      }
      return { name, cardinality: "unbounded", kind: "enum" };
    case "number":
      if (typeof min === "number" && typeof max === "number") {
        return { name, cardinality: max - min + 1, kind: "number" };
      }
      return { name, cardinality: "unbounded", kind: "number" };
    case "array":
      return { name, cardinality: "unbounded", kind: "array" };
    case "string":
      return { name, cardinality: "unbounded", kind: "string" };
    default:
      return null;
  }
}

function legacyFieldCardinality(name: string, obj: Record<string, unknown>): FieldEstimate | null {
  const values = obj["values"];
  const abstract = obj["abstract"];
  const min = obj["min"];
  const max = obj["max"];

  // { values: [...], abstract?: boolean }
  if (Array.isArray(values)) {
    const extra = abstract === true ? 1 : 0;
    return {
      name,
      cardinality: values.length + extra,
      kind: abstract === true ? "enum (abstract)" : "enum (values)",
    };
  }

  // { maxLength: N } (array)
  if ("maxLength" in obj && !("type" in obj)) {
    return { name, cardinality: "unbounded", kind: "array" };
  }

  // { min, max } (number range)
  if (typeof min === "number" && typeof max === "number" && !("type" in obj)) {
    return { name, cardinality: max - min + 1, kind: "number" };
  }

  return null;
}

/**
 * Compute the cardinality of a single state field from config.
 */
function fieldCardinality(name: string, value: unknown): FieldEstimate {
  // Array literal: [val1, val2, ...]
  if (Array.isArray(value)) {
    return { name, cardinality: value.length, kind: "enum (literal)" };
  }

  if (typeof value !== "object" || value === null) {
    return { name, cardinality: "unbounded", kind: "unknown" };
  }

  const obj = value as unknown as Record<string, unknown>;

  return (
    typedFieldCardinality(name, obj) ??
    legacyFieldCardinality(name, obj) ?? { name, cardinality: "unbounded", kind: "unknown" }
  );
}

function getHandlerCount(config: UnifiedVerificationConfig, analysis: CodebaseAnalysis): number {
  if (isLegacyConfig(config)) {
    const msgs = config.messages as unknown as LegacyVerificationConfig["messages"] & {
      include?: string[];
      exclude?: string[];
    };
    if (msgs.include) {
      return msgs.include.length;
    }
    if (msgs.exclude) {
      return Math.max(0, analysis.handlers.length - msgs.exclude.length);
    }
  }
  return analysis.handlers.length;
}

function getMaxInFlight(config: UnifiedVerificationConfig): number {
  if (isLegacyConfig(config)) {
    return config.messages.maxInFlight ?? 1;
  }
  if (isAdapterConfig(config)) {
    return (config as unknown as AdapterVerificationConfig).bounds?.maxInFlight ?? 1;
  }
  return 1;
}

/**
 * The message block the `.cfg` writer reads when it emits `Tabs`. An adapter
 * config has none, and the writer's default set (`{0, 1}`) is what it gets.
 */
function getTabSetInput(config: UnifiedVerificationConfig): TabSetInput {
  if (isLegacyConfig(config)) {
    return config.messages as unknown as TabSetInput;
  }
  return {};
}

/**
 * The context set the `.cfg` writer reads (polly#185). Declared on both config
 * arms, so no narrowing is needed — an absent key resolves to the default.
 */
function getContextSetInput(config: UnifiedVerificationConfig): ContextSetInput {
  return config as unknown as ContextSetInput;
}

function getFeasibility(states: number): StateSpaceEstimate["feasibility"] {
  if (states < 100_000) return "trivial";
  if (states <= 1_000_000) return "feasible";
  if (states <= 10_000_000) return "slow";
  return "infeasible";
}

function feasibilityLabel(f: StateSpaceEstimate["feasibility"]): string {
  switch (f) {
    case "trivial":
      return "trivial (should complete in seconds)";
    case "feasible":
      return "feasible (should complete in minutes)";
    case "slow":
      return "slow (may take 10–30 minutes)";
    case "infeasible":
      return "infeasible (likely won't terminate)";
  }
}

/** Variables the generated spec carries that this figure does not model. */
const OMITTED_VARIABLES = "ports, status, deliveredTo, time and payload";

/**
 * Which lever dominates a given estimate, by its log10 contribution.
 *
 * Reported so the suggestion names the term the user should move, rather than
 * offering the same three generic knobs for every model.
 */
function dominantTerm(e: {
  fieldProduct: number;
  handlerCount: number;
  contextCount: number;
  targetSets: number;
  tabCount: number;
  maxInFlight: number;
}): { label: string; decades: number } {
  const log10 = (n: number) => (n > 0 ? Math.log10(n) : 0);
  const topology = e.contextCount * e.targetSets * e.tabCount;

  const terms = [
    {
      label: `state fields (${e.fieldProduct} combinations across ${e.contextCount} contexts)`,
      decades: e.contextCount * log10(e.fieldProduct),
    },
    {
      label: `handler count (${e.handlerCount} handlers at maxInFlight ${e.maxInFlight})`,
      decades: e.maxInFlight * log10(e.handlerCount),
    },
    {
      label: `send topology (${e.contextCount} sources x ${e.targetSets} target sets x ${e.tabCount} tabs)`,
      decades: e.maxInFlight * log10(topology),
    },
  ];

  return terms.reduce((a, b) => (b.decades > a.decades ? b : a));
}

type EstimateScope = {
  /** Subsystem name; omitted for the monolithic model. */
  name?: string;
  /** State field names to include; all of them when omitted. */
  stateFields?: string[];
  handlerCount: number;
  maxInFlight: number;
};

function estimateForScope(
  config: UnifiedVerificationConfig,
  scope: EstimateScope
): StateSpaceEstimate {
  const state = config.state as unknown as Record<string, unknown>;
  const fields: FieldEstimate[] = [];
  const warnings: string[] = [];
  const suggestions: string[] = [];

  const included = scope.stateFields ? new Set(scope.stateFields) : undefined;
  for (const [name, value] of Object.entries(state)) {
    if (included && !included.has(name)) continue;
    fields.push(fieldCardinality(name, value));
  }

  // Compute field product (only bounded fields)
  const unboundedFields = fields.filter((f) => f.cardinality === "unbounded");
  const boundedFields = fields.filter((f) => f.cardinality !== "unbounded");

  const fieldProduct =
    boundedFields.length > 0
      ? boundedFields.reduce((acc, f) => acc * (f.cardinality as unknown as number), 1)
      : 1;

  if (unboundedFields.length > 0) {
    warnings.push(
      `${unboundedFields.length} field(s) have unbounded domains: ${unboundedFields.map((f) => f.name).join(", ")}`
    );
    suggestions.push(
      `Fields ${unboundedFields.map((f) => f.name).join(", ")} have unbounded domains — their actual impact depends on handler logic`
    );
  }

  const { handlerCount, maxInFlight } = scope;
  const tabSetInput = getTabSetInput(config);
  const tabCount = generatedTabCount(tabSetInput);

  // Contexts is the set the .cfg writer emits, not a function of maxTabs
  // (polly#183): `config.contexts` when declared, the extension default
  // otherwise (polly#185). Every generated spec replicates application state
  // across it.
  const contextSetInput = getContextSetInput(config);
  const contexts = resolveContexts(contextSetInput);
  const contextsDeclared = hasDeclaredContexts(contextSetInput);
  const contextCount = contexts.length;
  const totalStateSpace = fieldProduct ** contextCount;

  // Each in-flight message is one SendMessage step, and UserNext quantifies
  // over source, non-empty target set, tab and message type on every one.
  const sendBranching = sendBranchingFactor(handlerCount, tabCount, contexts);
  const interleavingFactor = sendBranching ** maxInFlight;

  const estimatedStates = totalStateSpace * interleavingFactor;

  const feasibility = getFeasibility(estimatedStates);

  warnings.push(
    `Lower bound: the generated spec also carries ${OMITTED_VARIABLES}, none of which this figure models.`
  );

  if (tabSetInput.tabSymmetry) {
    warnings.push(
      "tabSymmetry is enabled — TLC's symmetry reduction cuts the reachable set, so this is an upper bound on the tab dimension."
    );
  }

  const dominant = dominantTerm({
    fieldProduct,
    handlerCount,
    contextCount,
    targetSets: targetSetCount(contexts),
    tabCount,
    maxInFlight,
  });
  suggestions.push(
    `Dominant term: ${dominant.label} — ~10^${dominant.decades.toFixed(1)} of ~10^${Math.log10(Math.max(estimatedStates, 1)).toFixed(1)}`
  );

  if (maxInFlight > 1) {
    suggestions.push(
      `maxInFlight ${maxInFlight} → ${maxInFlight - 1} divides the estimate by ${sendBranching.toLocaleString()}x (one fewer send to branch over)`
    );
  }

  if (!contextsDeclared) {
    suggestions.push(
      `Contexts is the default {${contexts.join(", ")}} — no \`contexts\` key is declared. ` +
        `Declaring the ones this project has divides state replication by fieldProduct^(${contextCount} - n) ` +
        "and send branching by the drop in |Contexts| * (2^|Contexts| - 1) (polly#185)"
    );
  }

  if (handlerCount > 15) {
    suggestions.push(
      `${handlerCount} handlers enter the estimate as ${handlerCount}^${maxInFlight} — splitting into subsystems is the cheapest cut`
    );
  }

  for (const f of boundedFields) {
    if ((f.cardinality as unknown as number) > 50) {
      suggestions.push(
        `Field "${f.name}" (${f.cardinality} values) is raised to the power of ${contextCount} contexts — reducing its bounds compounds`
      );
    }
  }

  return {
    ...(scope.name === undefined ? {} : { subsystem: scope.name }),
    fields,
    fieldProduct,
    handlerCount,
    maxInFlight,
    contextCount,
    contexts,
    contextsDeclared,
    tabCount,
    sendBranching,
    totalStateSpace,
    interleavingFactor,
    estimatedStates,
    feasibility,
    warnings,
    suggestions,
  };
}

export function estimateStateSpace(
  config: UnifiedVerificationConfig,
  analysis: CodebaseAnalysis
): StateSpaceEstimate {
  return estimateForScope(config, {
    handlerCount: getHandlerCount(config, analysis),
    maxInFlight: getMaxInFlight(config),
  });
}

/**
 * One estimate per declared subsystem, in declaration order.
 *
 * A config with `subsystems` never runs the monolithic model, so estimating it
 * answers a question nobody asked (polly#183). Empty when none are declared.
 */
export function estimateSubsystems(config: UnifiedVerificationConfig): StateSpaceEstimate[] {
  const subsystems = (
    config as unknown as {
      subsystems?: Record<
        string,
        { state: string[]; handlers: string[]; bounds?: { maxInFlight?: number } }
      >;
    }
  ).subsystems;
  if (!subsystems) return [];

  const topLevelMaxInFlight = getMaxInFlight(config);

  return Object.entries(subsystems).map(([name, sub]) =>
    estimateForScope(config, {
      name,
      stateFields: sub.state,
      handlerCount: sub.handlers.length,
      maxInFlight: sub.bounds?.maxInFlight ?? topLevelMaxInFlight,
    })
  );
}

export { feasibilityLabel };
