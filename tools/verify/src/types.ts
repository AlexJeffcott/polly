// Core types for verification system

// Re-export shared types from analysis package
export type {
  CodebaseAnalysis,
  Confidence,
  Context,
  FieldAnalysis,
  MessageHandler,
  StateAssignment,
  TypeInfo,
  TypeKind,
  VerificationCondition,
} from "../../analysis/src/index.ts";

export type VerificationConfig = {
  preset?: "quick" | "balanced" | "thorough";
  state: StateConfig;
  messages: MessageConfig;
  onBuild: "warn" | "error" | "off";
  onRelease: "warn" | "error" | "off";
  verification?: {
    timeout?: number; // Timeout in seconds (0 = no timeout)
    workers?: number; // Number of TLC workers
  };

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

export type FieldConfig =
  | { type: "boolean" }
  | { maxLength: number | null }
  | { min: number | null; max: number | null }
  | { type: "enum"; values: string[] }
  | { values: string[] | null; abstract?: boolean }
  | { maxSize: number | null; valueType?: string }
  | { abstract: boolean };

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
  perMessageBounds?: Record<string, number>; // Different maxInFlight per message type
};

export type ConfigIssue = {
  type: "incomplete" | "null_placeholder" | "unrealistic_bound" | "invalid_value";
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
