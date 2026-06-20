// Configuration Helper for @fairfox/polly/verify
//
// Lightweight entry point for user configuration files.
// Does NOT include heavy dependencies (ts-morph, analysis, etc.)
// which are only needed by the CLI tool.

// Configuration Types (inlined to avoid heavy dependencies)

// polly#160: a directional capability whose grant requires a precondition.
// Desugars to a TLA+ safety invariant `(enabledBy) => (requires)`. enabledBy /
// requires are TS boolean expressions in the requires()/ensures() dialect
// referencing state via `state.` / signal `.value` form (e.g. "state.authReady").
// Inlined here (like SubsystemConfig) so this authoring entry point stays
// dependency-light; the canonical type is CapabilityConfig in config/types.ts.
interface CapabilityConfig {
  name: string;
  enabledBy: string;
  requires: string;
  message?: string;
}

// Subsystem configuration for compositional verification
interface SubsystemConfig {
  state: string[]; // Field names from parent state config
  handlers: string[]; // Message type names
  // Per-subsystem message bounds; override messages.maxInFlight and merge
  // into messages.perMessageBounds for this subsystem only.
  bounds?: {
    maxInFlight?: number;
    perMessageBounds?: Record<string, number>;
  };
}

// Point a subsystem's reachability witnesses at a hand-written TLA+ spec instead
// of the generated UserApp_<subsystem>. Inlined here (like SubsystemConfig) to
// keep this authoring entry point dependency-light; canonical type is
// CustomTLAPath in config/types.ts.
interface CustomTLAPath {
  tla: string; // path (relative to cwd) to the hand-written .tla the witness EXTENDS
  cfg: string; // path (relative to cwd) to its .cfg
  module?: string; // module to EXTEND; defaults to the MODULE name parsed from `tla`
  fields?: Record<string, string>; // BDD field name → this spec's TLA+ variable name
}

// Legacy verification configuration
interface LegacyVerificationConfig {
  state: Record<string, unknown>;
  /**
   * polly#117: optional mesh-document declarations. When present, each
   * key names a `$meshState` document and its value declares the
   * field-level state schema for that document. The verifier emits a
   * separate slot in `contextStates[ctx].mesh[<docId>]` for these
   * fields and adds a `PropagateMeshOp` action that allows the doc's
   * value on one context to flow to another — modelling Automerge
   * sync between peers. Mesh references inside `forAllPeers` quantifiers
   * route through this slot so cross-peer convergence claims are
   * actually checked.
   *
   * @example
   * ```ts
   * defineVerification({
   *   state: { localCounter: { type: "number", min: 0, max: 3 } },
   *   mesh: {
   *     todos: {
   *       entries: { type: "enum", values: ["empty", "one", "many"] },
   *     },
   *   },
   *   messages: { maxInFlight: 2 },
   * });
   * ```
   */
  mesh?: Record<string, Record<string, unknown>>;
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

  // Verification engine options
  verification?: {
    timeout?: number; // Timeout in seconds (0 = no timeout)
    workers?: number; // Number of TLC workers
  };

  // Subsystem-scoped verification (compositional)
  subsystems?: Record<string, SubsystemConfig>;

  // Bind a subsystem's witnesses to a hand-written .tla/.cfg (read only by the
  // --witness pass; a custom subsystem is skipped during generated-spec verify).
  customTLAPaths?: Record<string, CustomTLAPath>;

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

  // polly#160: directional capability invariants + write-coupling lint groups
  capabilities?: CapabilityConfig[];
  coupledFields?: string[][];
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

  // polly#160: directional capability invariants + write-coupling lint groups
  capabilities?: CapabilityConfig[];
  coupledFields?: string[][];
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

// Re-export verification primitives for user code
export {
  $constraints,
  ensures,
  forAllPeers,
  hasLength,
  inRange,
  oneOf,
  requires,
  somePeer,
  stateConstraint,
} from "./primitives/index.js";
