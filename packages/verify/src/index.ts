// ═══════════════════════════════════════════════════════════════
// Public API for @fairfox/web-ext-verify
// ═══════════════════════════════════════════════════════════════

// ─────────────────────────────────────────────────────────────────
// Core Types (Domain-Agnostic)
// ─────────────────────────────────────────────────────────────────
export type {
  CoreVerificationModel,
  NodeDefinition,
  MessageType,
  RoutingPattern,
  RoutingRule,
  StateSchema,
  FieldConfig,
  StateAssignment,
  VerificationCondition,
  MessageHandler,
  TypeKind,
  TypeInfo,
  Confidence,
  FieldAnalysis,
  CodebaseAnalysis,
} from "./core/model"

// ─────────────────────────────────────────────────────────────────
// Verification Primitives (Domain-Agnostic)
// ─────────────────────────────────────────────────────────────────
export {
  requires,
  ensures,
  invariant,
  inRange,
  oneOf,
  hasLength,
  verify,
} from "./core/primitives"

// Also re-export from old location for backward compatibility
export * from "./primitives/index"

// ─────────────────────────────────────────────────────────────────
// Adapters
// ─────────────────────────────────────────────────────────────────
export type { RoutingAdapter, AdapterConfig } from "./adapters/base"
export { BaseRoutingAdapter } from "./adapters/base"
export {
  WebExtensionAdapter,
  type WebExtensionAdapterConfig,
  type ExtensionContext,
} from "./adapters/web-extension"

// ─────────────────────────────────────────────────────────────────
// Legacy API (Backward Compatibility)
// ─────────────────────────────────────────────────────────────────
export type { VerificationConfig, ValidationResult } from "./types"
export { HandlerExtractor, extractHandlers } from "./extract/handlers"
export { analyzeCodebase } from "./extract/types"
export { TLAGenerator, generateTLA } from "./codegen/tla"
export { generateConfig } from "./codegen/config"
export { validateConfig } from "./config/parser"

/**
 * Define verification configuration
 * This is a helper function that provides type checking for the config
 */
export function defineVerification(config: any): any {
  return config
}
