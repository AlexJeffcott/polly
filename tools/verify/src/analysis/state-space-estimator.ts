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
  fields: FieldEstimate[];
  fieldProduct: number;
  handlerCount: number;
  maxInFlight: number;
  contextCount: number;
  totalStateSpace: number;
  interleavingFactor: number;
  estimatedStates: number;
  feasibility: "trivial" | "feasible" | "slow" | "infeasible";
  warnings: string[];
  suggestions: string[];
};

function typedFieldCardinality(name: string, obj: Record<string, unknown>): FieldEstimate | null {
  if (!("type" in obj)) return null;

  switch (obj.type) {
    case "boolean":
      return { name, cardinality: 2, kind: "boolean" };
    case "enum":
      if (Array.isArray(obj.values)) {
        return { name, cardinality: obj.values.length, kind: "enum" };
      }
      return { name, cardinality: "unbounded", kind: "enum" };
    case "number":
      if (typeof obj.min === "number" && typeof obj.max === "number") {
        return { name, cardinality: obj.max - obj.min + 1, kind: "number" };
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
  // { values: [...], abstract?: boolean }
  if ("values" in obj && Array.isArray(obj.values)) {
    const base = obj.values.length;
    const extra = obj.abstract === true ? 1 : 0;
    return {
      name,
      cardinality: base + extra,
      kind: obj.abstract ? "enum (abstract)" : "enum (values)",
    };
  }

  // { maxLength: N } (array)
  if ("maxLength" in obj && !("type" in obj)) {
    return { name, cardinality: "unbounded", kind: "array" };
  }

  // { min, max } (number range)
  if (
    "min" in obj &&
    "max" in obj &&
    typeof obj.min === "number" &&
    typeof obj.max === "number" &&
    !("type" in obj)
  ) {
    return { name, cardinality: obj.max - obj.min + 1, kind: "number" };
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

  const obj = value as Record<string, unknown>;

  return (
    typedFieldCardinality(name, obj) ??
    legacyFieldCardinality(name, obj) ?? { name, cardinality: "unbounded", kind: "unknown" }
  );
}

/**
 * Compute C(n, k) * k! = n! / (n-k)! (permutations)
 */
function permutations(n: number, k: number): number {
  if (k > n) return 1;
  let result = 1;
  for (let i = 0; i < k; i++) {
    result *= n - i;
  }
  return result;
}

function getHandlerCount(config: UnifiedVerificationConfig, analysis: CodebaseAnalysis): number {
  if (isLegacyConfig(config)) {
    const msgs = config.messages as LegacyVerificationConfig["messages"] & {
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
    return (config as AdapterVerificationConfig).bounds?.maxInFlight ?? 1;
  }
  return 1;
}

function getMaxTabs(config: UnifiedVerificationConfig): number {
  if (isLegacyConfig(config)) {
    return config.messages.maxTabs ?? 1;
  }
  return 1;
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

export function estimateStateSpace(
  config: UnifiedVerificationConfig,
  analysis: CodebaseAnalysis
): StateSpaceEstimate {
  const state = config.state as Record<string, unknown>;
  const fields: FieldEstimate[] = [];
  const warnings: string[] = [];
  const suggestions: string[] = [];

  for (const [name, value] of Object.entries(state)) {
    fields.push(fieldCardinality(name, value));
  }

  // Compute field product (only bounded fields)
  const unboundedFields = fields.filter((f) => f.cardinality === "unbounded");
  const boundedFields = fields.filter((f) => f.cardinality !== "unbounded");

  const fieldProduct =
    boundedFields.length > 0
      ? boundedFields.reduce((acc, f) => acc * (f.cardinality as number), 1)
      : 1;

  if (unboundedFields.length > 0) {
    warnings.push(
      `${unboundedFields.length} field(s) have unbounded domains: ${unboundedFields.map((f) => f.name).join(", ")}`
    );
    suggestions.push(
      `Fields ${unboundedFields.map((f) => f.name).join(", ")} have unbounded domains — their actual impact depends on handler logic`
    );
  }

  const handlerCount = getHandlerCount(config, analysis);
  const maxInFlight = getMaxInFlight(config);
  const maxTabs = getMaxTabs(config);

  // Contexts: tabs + 1 background
  const contextCount = maxTabs + 1;

  const totalStateSpace = fieldProduct ** contextCount;

  // Interleaving: permutations(handlerCount, maxInFlight)
  const interleavingFactor = permutations(handlerCount, maxInFlight);

  const estimatedStates = totalStateSpace * interleavingFactor;

  const feasibility = getFeasibility(estimatedStates);

  // Generate suggestions
  if (handlerCount > 15) {
    suggestions.push("Consider splitting into subsystems");
  }

  for (const f of boundedFields) {
    if ((f.cardinality as number) > 50) {
      suggestions.push(`Consider reducing bounds for field "${f.name}" (${f.cardinality} values)`);
    }
  }

  if (maxInFlight > 2) {
    const reducedInterleaving = permutations(handlerCount, 2);
    const reduction =
      reducedInterleaving > 0 ? Math.round(interleavingFactor / reducedInterleaving) : 1;
    suggestions.push(
      `Reducing maxInFlight from ${maxInFlight} to 2 would reduce interleaving by ~${reduction}x`
    );
  }

  return {
    fields,
    fieldProduct,
    handlerCount,
    maxInFlight,
    contextCount,
    totalStateSpace,
    interleavingFactor,
    estimatedStates,
    feasibility,
    warnings,
    suggestions,
  };
}

export { feasibilityLabel };
