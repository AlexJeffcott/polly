// Configuration Types for Adapter-Based Verification

import type { RoutingAdapter } from "../adapters/base";
import type { StateSchema } from "../core/model";

// New Adapter-Based Configuration

/**
 * polly#160: a directional capability whose grant requires a precondition.
 * Desugars to a TLA+ safety invariant `(enabledBy) => (requires)` checked at
 * every reachable state — catching "a capability granted without its
 * precondition" (an omission across multiple handlers that mutation testing
 * cannot see).
 *
 * `enabledBy` and `requires` are TS boolean expressions in the same dialect as
 * `requires()`/`ensures()` (e.g. `"state.authReady"`,
 * `"state.user.value.loggedIn"`). They MUST reference state via the `state.` /
 * signal `.value` form so the field flattens to `contextStates[ctx].*`; bare
 * identifiers are rejected at config-validation time.
 */
export interface CapabilityConfig {
  /** Capability name; used to derive the TLA+ invariant identifier. */
  name: string;
  /** Expression that is true when the capability is granted/active. */
  enabledBy: string;
  /** Expression that MUST hold whenever the capability is enabled. */
  requires: string;
  /** Optional human-readable message for the generated invariant comment. */
  message?: string;
}

/**
 * Adapter-based verification configuration (new format)
 */
export interface AdapterVerificationConfig {
  /** The routing adapter to use */
  adapter: RoutingAdapter;

  /** State bounds (domain-agnostic) */
  state: StateSchema;

  /** Concurrency bounds */
  bounds?: {
    maxInFlight?: number;
    [key: string]: unknown;
  };

  /** Verification behavior on build */
  onBuild?: "warn" | "error" | "off";

  /** Verification behavior on release */
  onRelease?: "warn" | "error" | "off";

  /** Optional: Custom invariants */
  invariants?: Array<{
    name: string;
    expression: string;
    description?: string;
  }>;

  /** polly#160: directional capability invariants (desugar to TLA+). */
  capabilities?: CapabilityConfig[];

  /** polly#160: symmetric write-coupling lint groups (static warning only). */
  coupledFields?: string[][];
}

// Legacy Configuration (Backward Compatibility)

/**
 * Legacy verification configuration (backward compatible)
 */
export interface LegacyVerificationConfig {
  /** State configuration (old format) */
  state: Record<string, unknown>;

  /** Message configuration (old format) */
  messages: {
    maxInFlight: number | null;
    maxTabs: number | null;
  };

  /** Verification behavior on build */
  onBuild: "warn" | "error" | "off";

  /** Verification behavior on release */
  onRelease: "warn" | "error" | "off";

  /** polly#160: directional capability invariants (desugar to TLA+). */
  capabilities?: CapabilityConfig[];

  /** polly#160: symmetric write-coupling lint groups (static warning only). */
  coupledFields?: string[][];
}

// Unified Configuration Type

/**
 * Union of new and legacy configuration formats
 */
export type UnifiedVerificationConfig = AdapterVerificationConfig | LegacyVerificationConfig;

/**
 * Type guard to check if config is adapter-based (new format)
 */
export function isAdapterConfig(
  config: UnifiedVerificationConfig
): config is AdapterVerificationConfig {
  return "adapter" in config;
}

/**
 * Type guard to check if config is legacy format
 */
export function isLegacyConfig(
  config: UnifiedVerificationConfig
): config is LegacyVerificationConfig {
  return "messages" in config && !("adapter" in config);
}

// Configuration Validation

export interface ConfigIssue {
  type:
    | "incomplete"
    | "null_placeholder"
    | "unrealistic_bound"
    | "invalid_value"
    // polly#160
    | "capability_unknown_field"
    | "capability_empty_expression"
    | "coupled_unknown_field";
  severity: "error" | "warning";
  field?: string;
  location?: { line: number; column: number };
  message: string;
  suggestion: string;
}

export interface ValidationResult {
  valid: boolean;
  issues: ConfigIssue[];
  configType?: "adapter" | "legacy";
}
