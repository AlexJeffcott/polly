// ═══════════════════════════════════════════════════════════════
// Core Analysis Model (Domain-Agnostic)
// ═══════════════════════════════════════════════════════════════
//
// This module defines abstract types for analyzing message-passing systems.
// These types are independent of the specific domain (web extensions,
// actors, event buses, etc.).

// ─────────────────────────────────────────────────────────────────
// Type System (Universal)
// ─────────────────────────────────────────────────────────────────

export type TypeKind =
  | "boolean"
  | "string"
  | "number"
  | "enum"
  | "array"
  | "object"
  | "map"
  | "set"
  | "union"
  | "null"
  | "unknown"

export type TypeInfo = {
  name: string
  kind: TypeKind
  nullable: boolean
  elementType?: TypeInfo  // For arrays, sets
  valueType?: TypeInfo    // For maps
  properties?: Record<string, TypeInfo>  // For objects
  enumValues?: string[]   // For enums
  unionTypes?: TypeInfo[] // For unions
}

// ─────────────────────────────────────────────────────────────────
// Node System (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * A node represents an entity in the system that can send/receive messages.
 *
 * Examples:
 * - Web extension: "background", "content", "popup"
 * - Actor system: Individual actor instances
 * - Event bus: Emitters/listeners
 * - Worker threads: Main thread + worker instances
 */
export type NodeDefinition = {
  /** Unique identifier for this node */
  id: string

  /** Type of node (adapter-specific) */
  type: string

  /** Which nodes can this send messages to? */
  canSendTo: string[]

  /** Which nodes can send messages to this? */
  canReceiveFrom: string[]

  /** Optional: Additional metadata */
  metadata?: Record<string, unknown>
}

// ─────────────────────────────────────────────────────────────────
// Message Types (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * Defines a type of message that flows through the system
 */
export type MessageTypeDefinition = {
  /** Name/identifier of the message type */
  name: string

  /** Schema of the message payload */
  payload: TypeInfo

  /** Routing constraints */
  routing: {
    /** Which node types can send this message? */
    from: string[]

    /** Which node types can receive this message? */
    to: string[]
  }

  /** Optional: Expected response type */
  response?: TypeInfo
}

// ─────────────────────────────────────────────────────────────────
// State Schema (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * Configuration for a state field
 */
export type FieldConfig =
  | { maxLength: number | null }
  | { min: number | null; max: number | null }
  | { type: "enum"; values: string[] }
  | { values: string[] | null; abstract?: boolean }
  | { maxSize: number | null; valueType?: unknown }
  | { abstract: boolean }

export type StateSchema = Record<string, FieldConfig>

// ─────────────────────────────────────────────────────────────────
// State Mutations (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * Represents an assignment to a state field
 */
export type StateAssignment = {
  /** Field path (e.g., "user.loggedIn") */
  field: string

  /** The assigned value */
  value: string | boolean | number | null

  /** Optional condition guard */
  conditional?: string
}

// ─────────────────────────────────────────────────────────────────
// Verification Conditions (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * A verification condition (precondition or postcondition)
 */
export type VerificationCondition = {
  /** The condition expression as a string */
  expression: string

  /** Optional error message */
  message?: string

  /** Source location */
  location: {
    line: number
    column: number
  }
}

// ─────────────────────────────────────────────────────────────────
// Message Handler (Abstract)
// ─────────────────────────────────────────────────────────────────

/**
 * Represents a message handler extracted from code
 */
export type MessageHandler = {
  /** Which message type does this handle? */
  messageType: string

  /** Which node handles this message? */
  node: string

  /** State assignments made by this handler */
  assignments: StateAssignment[]

  /** Preconditions (requires() calls) */
  preconditions: VerificationCondition[]

  /** Postconditions (ensures() calls) */
  postconditions: VerificationCondition[]

  /** Source location */
  location: {
    file: string
    line: number
  }
}

// ─────────────────────────────────────────────────────────────────
// Confidence Levels (Universal)
// ─────────────────────────────────────────────────────────────────

export type Confidence = "high" | "medium" | "low"

export type FieldAnalysis = {
  path: string
  type: TypeInfo
  confidence: Confidence
  evidence: string[]
  suggestions: string[]
  bounds?: {
    min?: number
    max?: number
    maxLength?: number
    maxSize?: number
    values?: string[]
  }
}

// ─────────────────────────────────────────────────────────────────
// Codebase Analysis Result
// ─────────────────────────────────────────────────────────────────

export type CodebaseAnalysis = {
  stateType: TypeInfo | null
  messageTypes: string[]
  fields: FieldAnalysis[]
  handlers: MessageHandler[]
}
