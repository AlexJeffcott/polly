// ═══════════════════════════════════════════════════════════════
// Configuration Types for Adapter-Based Verification
// ═══════════════════════════════════════════════════════════════

import type { RoutingAdapter } from "../adapters/base";
import type { StateSchema } from "../core/model";

// ─────────────────────────────────────────────────────────────────
// New Adapter-Based Configuration
// ─────────────────────────────────────────────────────────────────

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
}

// ─────────────────────────────────────────────────────────────────
// Legacy Configuration (Backward Compatibility)
// ─────────────────────────────────────────────────────────────────

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

  /** Optional preset */
  preset?: "quick" | "balanced" | "thorough";
}

// ─────────────────────────────────────────────────────────────────
// Unified Configuration Type
// ─────────────────────────────────────────────────────────────────

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

// ─────────────────────────────────────────────────────────────────
// Configuration Validation
// ─────────────────────────────────────────────────────────────────

export interface ConfigIssue {
  type: "incomplete" | "null_placeholder" | "unrealistic_bound" | "invalid_value";
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
