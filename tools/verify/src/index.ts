// ═══════════════════════════════════════════════════════════════
// Public API for @fairfox/polly-verify
// ═══════════════════════════════════════════════════════════════

// ─────────────────────────────────────────────────────────────────
// Adapters
// ─────────────────────────────────────────────────────────────────
export type { AdapterConfig, RoutingAdapter } from "./adapters/base";
export { BaseRoutingAdapter } from "./adapters/base";
// Adapter Detection
export {
  type AdapterDetectionResult,
  AdapterDetector,
  detectAdapter,
} from "./adapters/detection";
export {
  EventBusAdapter,
  type EventBusAdapterConfig,
} from "./adapters/event-bus";
export {
  type ExtensionContext,
  WebExtensionAdapter,
  type WebExtensionAdapterConfig,
} from "./adapters/web-extension";
export {
  WebSocketAdapter,
  type WebSocketAdapterConfig,
} from "./adapters/websocket";
// ─────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────
export type {
  AdapterVerificationConfig,
  ConfigIssue,
  LegacyVerificationConfig,
  UnifiedVerificationConfig,
  ValidationResult as ConfigValidationResult,
} from "./config/types";
export { isAdapterConfig, isLegacyConfig } from "./config/types";
// ─────────────────────────────────────────────────────────────────
// Core Types (Domain-Agnostic)
// ─────────────────────────────────────────────────────────────────
export type {
  CodebaseAnalysis,
  Confidence,
  CoreVerificationModel,
  FieldAnalysis,
  FieldConfig,
  MessageHandler,
  MessageType,
  NodeDefinition,
  RoutingPattern,
  RoutingRule,
  StateAssignment,
  StateSchema,
  TypeInfo,
  TypeKind,
  VerificationCondition,
} from "./core/model";
// ─────────────────────────────────────────────────────────────────
// Verification Primitives (Domain-Agnostic)
// ─────────────────────────────────────────────────────────────────
export {
  ensures,
  hasLength,
  inRange,
  invariant,
  oneOf,
  requires,
  verify,
} from "./core/primitives";
// Also re-export from old location for backward compatibility
export * from "./primitives/index";

import type { UnifiedVerificationConfig } from "./config/types";

/**
 * Define verification configuration with type checking
 *
 * Supports both new adapter-based and legacy configurations.
 *
 * @example New adapter-based format:
 * ```typescript
 * import { WebExtensionAdapter, defineVerification } from '@fairfox/polly-verify'
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

export { generateConfig } from "./codegen/config";
export { generateTLA, TLAGenerator } from "./codegen/tla";
export { validateConfig } from "./config/parser";
export { extractHandlers, HandlerExtractor } from "./extract/handlers";
export { analyzeCodebase } from "./extract/types";
// ─────────────────────────────────────────────────────────────────
// Legacy API (Backward Compatibility)
// ─────────────────────────────────────────────────────────────────
export type { ValidationResult, VerificationConfig } from "./types";
