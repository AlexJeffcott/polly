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
export {
  EventBusAdapter,
  type EventBusAdapterConfig,
} from "./adapters/event-bus"
export {
  WebSocketAdapter,
  type WebSocketAdapterConfig,
} from "./adapters/websocket"

// Adapter Detection
export {
  AdapterDetector,
  detectAdapter,
  type AdapterDetectionResult,
} from "./adapters/detection"

// ─────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────
export type {
  AdapterVerificationConfig,
  LegacyVerificationConfig,
  UnifiedVerificationConfig,
  ConfigIssue,
  ValidationResult as ConfigValidationResult,
} from "./config/types"
export { isAdapterConfig, isLegacyConfig } from "./config/types"

import type { UnifiedVerificationConfig } from "./config/types"

/**
 * Define verification configuration with type checking
 *
 * Supports both new adapter-based and legacy configurations.
 *
 * @example New adapter-based format:
 * ```typescript
 * import { WebExtensionAdapter, defineVerification } from '@fairfox/web-ext-verify'
 *
 * export default defineVerification({
 *   adapter: new WebExtensionAdapter({
 *     tsConfigPath: "./tsconfig.json",
 *     maxInFlight: 6,
 *   }),
 *   state: {
 *     "user.role": { type: "enum", values: ["admin", "user", "guest"] },
 *   },
 * })
 * ```
 *
 * @example Legacy format (backward compatible):
 * ```typescript
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
export function defineVerification<
  T extends UnifiedVerificationConfig
>(config: T): T {
  // Validate configuration structure
  if ("adapter" in config) {
    // New adapter-based format
    if (!config.adapter) {
      throw new Error("Configuration must include an adapter")
    }
    if (!config.state) {
      throw new Error("Configuration must include state bounds")
    }
  } else if ("messages" in config) {
    // Legacy format
    if (!config.state) {
      throw new Error("Configuration must include state bounds")
    }
    if (!config.messages) {
      throw new Error("Legacy configuration must include messages bounds")
    }
  } else {
    throw new Error(
      "Invalid configuration format. Must include either 'adapter' (new format) or 'messages' (legacy format)"
    )
  }

  return config
}

// ─────────────────────────────────────────────────────────────────
// Legacy API (Backward Compatibility)
// ─────────────────────────────────────────────────────────────────
export type { VerificationConfig, ValidationResult } from "./types"
export { HandlerExtractor, extractHandlers } from "./extract/handlers"
export { analyzeCodebase } from "./extract/types"
export { TLAGenerator, generateTLA } from "./codegen/tla"
export { generateConfig } from "./codegen/config"
export { validateConfig } from "./config/parser"
