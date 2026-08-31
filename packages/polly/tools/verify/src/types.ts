// Core types for verification system

// Re-export shared types from analysis package
export type {
  CodebaseAnalysis,
  Confidence,
  Context,
  FieldAnalysis,
  MessageHandler,
  ResourceInfo,
  StateAssignment,
  TypeInfo,
  TypeKind,
  VerificationCondition,
} from "../../analysis/src/index.ts";

// polly#160: capability declarations are authored on the public config arms
// (config/types.ts) and consumed here on the internal VerificationConfig.
export type { CapabilityConfig } from "./config/types";

import type { CapabilityConfig } from "./config/types";

export type SubsystemConfig = {
  state: string[]; // Field names from parent state config
  handlers: string[]; // Message type names
  // Per-subsystem message bounds. Override the top-level messages.maxInFlight
  // and merge into messages.perMessageBounds for this subsystem only, so
  // subsystems with no parameterised handlers can run at higher maxInFlight
  // (and exercise multi-step ensures) without blowing up the global state
  // space of subsystems that carry unbounded payload domains.
  bounds?: {
    maxInFlight?: number;
    perMessageBounds?: Record<string, number>;
  };
  /** polly#171: check message-resolution liveness for this subsystem. Overrides
   *  the top-level `liveness`. See VerificationConfig.liveness for the cost. */
  liveness?: boolean;
};

export type VerificationConfig = {
  state: StateConfig;
  /**
   * polly#117: optional mesh-document declarations. Each key is the
   * document id (the first argument to a `$meshState` factory call)
   * and the value declares the field schema. Fields declared here are
   * emitted into a separate `contextStates[ctx].mesh[<docId>]` slot,
   * and the codegen adds a `PropagateMeshOp` action that allows
   * a doc's value on one context to flow to another. Without a
   * matching declaration here, `$meshState` references continue to
   * flatten into single-context local state and the CLI emits a
   * warning at verify time.
   */
  mesh?: MeshConfig;
  messages: MessageConfig;
  onBuild: "warn" | "error" | "off";
  onRelease: "warn" | "error" | "off";
  verification?: {
    timeout?: number; // Timeout in seconds (0 = no timeout)
    workers?: number; // Number of TLC workers
  };

  /**
   * polly#171: check that nothing sent stays pending for ever.
   *
   * Off by default because it is expensive: it adds a temporal property and the
   * routing fairness it needs, and TLC must then explore behaviours rather than
   * only reachable states. Measured on an 11-subsystem consumer model, the full
   * verify gate went from ~110s to ~512s.
   *
   * Every property the generator emits without this is a SAFETY property, and a
   * safety property is true of a system that does nothing at all — so a spec in
   * which routing has stopped verifies identically to one in which it works.
   * Turn this on for the subsystems whose progress actually matters.
   *
   * LIMITATION, and it is Lamport's own warning (Specifying Systems 14.3.5):
   * generated specs also declare a CONSTRAINT to bound the state space, and TLC
   * prints "Declaring state or action constraints during liveness checking is
   * dangerous" when both are present. A constraint truncates behaviours at its
   * boundary, so a liveness violation reachable only beyond that boundary is not
   * found. Treat a green liveness run as "no wedge within the bounds", not as a
   * proof of progress — the same reading every bounded model-checking result
   * deserves.
   */
  liveness?: boolean;

  // Subsystem-scoped verification (compositional)
  subsystems?: Record<string, SubsystemConfig>;

  // polly#160: directional capability invariants (desugar to TLA+ safety
  // invariants) + symmetric write-coupling lint groups (static warning only).
  capabilities?: CapabilityConfig[];
  coupledFields?: string[][];

  // Tier 2 Optimizations (controlled approximations)
  tier2?: {
    // Temporal constraints: ordering requirements between messages
    temporalConstraints?: TemporalConstraint[];

    // Bounded exploration: limit depth for specific scenarios
    boundedExploration?: BoundedExplorationConfig;
  };
};

/**
 * Temporal constraint (Tier 2) - ordering requirement between message types
 * Example: 'USER_LOGIN' must happen before 'USER_LOGOUT'
 */
export type TemporalConstraint = {
  before: string; // Message type that must occur first
  after: string; // Message type that must occur after
  description?: string; // Human-readable description
};

/**
 * Bounded exploration configuration (Tier 2)
 */
export type BoundedExplorationConfig = {
  maxDepth?: number; // Maximum state depth to explore
  criticalPaths?: string[][]; // Sequences of message types that must be fully explored
};

export type StateConfig = Record<string, FieldConfig>;

/**
 * polly#117: mesh-document declarations. Maps docId → field schema.
 */
export type MeshConfig = Record<string, Record<string, FieldConfig>>;

export type FieldConfig =
  | { type: "boolean" }
  | { type: "array"; maxLength?: number | null; initial?: unknown[] }
  | { type: "string"; initial?: string }
  | { type: "number"; min?: number; max?: number }
  | { maxLength: number | null }
  | { min: number | null; max: number | null }
  | { type: "enum"; values: string[] }
  | { values: string[] | null; abstract?: boolean; nullable?: boolean }
  | { maxSize: number | null; valueType?: string }
  | { abstract: boolean; nullable?: boolean };

export type MessageConfig = {
  maxInFlight: number | null;
  maxTabs?: number | null;
  maxClients?: number | null;
  maxRenderers?: number | null;
  maxWorkers?: number | null;
  maxContexts?: number | null;

  // Tier 1 Optimizations (no precision loss)
  include?: string[]; // Only verify these message types
  exclude?: string[]; // Exclude these message types (mutually exclusive with include)
  symmetry?: string[][]; // Groups of symmetric message types [[type1, type2], [type3, type4]]
  tabSymmetry?: boolean; // Enable tab symmetry reduction using model values
  perMessageBounds?: Record<string, number>; // Different maxInFlight per message type
};

export type ConfigIssue = {
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
};

export type ValidationResult = {
  valid: boolean;
  issues: ConfigIssue[];
};
