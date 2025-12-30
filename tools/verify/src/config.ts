// ═══════════════════════════════════════════════════════════════
// Configuration Helper for @fairfox/polly/verify
// ═══════════════════════════════════════════════════════════════
//
// Lightweight entry point for user configuration files.
// Does NOT include heavy dependencies (ts-morph, analysis, etc.)
// which are only needed by the CLI tool.

// ─────────────────────────────────────────────────────────────────
// Configuration Types (inlined to avoid heavy dependencies)
// ─────────────────────────────────────────────────────────────────

// Legacy verification configuration
interface LegacyVerificationConfig {
  state: Record<string, unknown>;
  messages: {
    // Basic bounds
    maxInFlight?: number;
    maxTabs?: number;
    maxClients?: number;
    maxRenderers?: number;
    maxWorkers?: number;
    maxContexts?: number;

    // Tier 1 Optimizations (no precision loss)
    include?: string[]; // Only verify these message types
    exclude?: string[]; // Exclude these message types (mutually exclusive with include)
    symmetry?: string[][]; // Groups of symmetric message types [[type1, type2], [type3, type4]]
    perMessageBounds?: Record<string, number>; // Different maxInFlight per message type
  };
  onBuild?: "warn" | "error" | "off";
  onRelease?: "warn" | "error" | "off";
  preset?: "quick" | "balanced" | "thorough";

  // Verification engine options
  verification?: {
    timeout?: number; // Timeout in seconds (0 = no timeout)
    workers?: number; // Number of TLC workers
  };

  // Tier 2 Optimizations (controlled approximations)
  tier2?: {
    // Temporal constraints: ordering requirements between messages
    temporalConstraints?: Array<{
      before: string; // Message type that must occur first
      after: string; // Message type that must occur after
      description?: string; // Human-readable description
    }>;

    // Bounded exploration: limit depth for specific scenarios
    boundedExploration?: {
      maxDepth?: number; // Maximum state depth to explore
      criticalPaths?: string[][]; // Sequences of message types that must be fully explored
    };
  };
}

// Adapter-based configuration (for future use)
interface AdapterVerificationConfig {
  adapter: unknown; // Adapter interface not exported to avoid heavy deps
  state: Record<string, unknown>;
  bounds?: {
    maxInFlight?: number;
    [key: string]: unknown;
  };
  onBuild?: "warn" | "error" | "off";
}

// Union type for both config formats
type UnifiedVerificationConfig = LegacyVerificationConfig | AdapterVerificationConfig;

/**
 * Define verification configuration with type checking
 *
 * Used in generated verification.config.ts files.
 *
 * @example
 * ```typescript
 * import { defineVerification } from '@fairfox/polly/verify'
 *
 * export default defineVerification({
 *   state: {
 *     "user.role": { type: "enum", values: ["admin", "user", "guest"] },
 *   },
 *   messages: {
 *     maxInFlight: 6,
 *     maxTabs: 2,
 *   },
 * })
 * ```
 */
export function defineVerification<T extends UnifiedVerificationConfig>(config: T): T {
  // Validate configuration structure
  if ("adapter" in config) {
    // New adapter-based format
    if (!config.adapter) {
      throw new Error("Configuration must include an adapter");
    }
    if (!config.state) {
      throw new Error("Configuration must include state bounds");
    }
  } else if ("messages" in config) {
    // Legacy format
    if (!config.state) {
      throw new Error("Configuration must include state bounds");
    }
    if (!config.messages) {
      throw new Error("Legacy configuration must include messages bounds");
    }
  } else {
    throw new Error(
      "Invalid configuration format. Must include either 'adapter' (new format) or 'messages' (legacy format)"
    );
  }

  return config;
}
