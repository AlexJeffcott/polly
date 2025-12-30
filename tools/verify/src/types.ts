// Core types for verification system

// Re-export shared types from analysis package
export type {
  Context,
  TypeKind,
  TypeInfo,
  FieldAnalysis,
  Confidence,
  MessageHandler,
  StateAssignment,
  VerificationCondition,
  CodebaseAnalysis,
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
