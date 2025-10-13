// Core types for verification system

export type Context =
  | "background"
  | "content"
  | "popup"
  | "devtools"
  | "options"
  | "offscreen"
  | "sidepanel"

export type Confidence = "high" | "medium" | "low"

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

export type CodebaseAnalysis = {
  stateType: TypeInfo | null
  messageTypes: string[]
  fields: FieldAnalysis[]
  handlers: MessageHandler[]
}

export type StateAssignment = {
  field: string  // e.g., "user.loggedIn"
  value: string | boolean | number | null  // The assigned value
  conditional?: string  // Optional condition guard
}

export type MessageHandler = {
  messageType: string
  context: string  // background, content, popup, etc.
  assignments: StateAssignment[]
  location: {
    file: string
    line: number
  }
}

export type VerificationConfig = {
  preset?: "quick" | "balanced" | "thorough"
  state: StateConfig
  messages: MessageConfig
  onBuild: "warn" | "error" | "off"
  onRelease: "warn" | "error" | "off"
}

export type StateConfig = Record<string, FieldConfig>

export type FieldConfig =
  | { maxLength: number | null }
  | { min: number | null, max: number | null }
  | { type: "enum", values: string[] }
  | { values: string[] | null, abstract?: boolean }
  | { maxSize: number | null, valueType?: any }
  | { abstract: boolean }

export type MessageConfig = {
  maxInFlight: number | null
  maxTabs: number | null
}

export type ConfigIssue = {
  type: "incomplete" | "null_placeholder" | "unrealistic_bound" | "invalid_value"
  severity: "error" | "warning"
  field?: string
  location?: { line: number, column: number }
  message: string
  suggestion: string
}

export type ValidationResult = {
  valid: boolean
  issues: ConfigIssue[]
}
