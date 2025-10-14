// Public API for @fairfox/web-ext-verify

// Types
export type { VerificationConfig, ValidationResult, CodebaseAnalysis } from "./types"

// Extraction
export { HandlerExtractor, extractHandlers } from "./extract/handlers"
export { analyzeCodebase } from "./extract/types"

// Code generation
export { TLAGenerator, generateTLA } from "./codegen/tla"
export { generateConfig } from "./codegen/config"

// Configuration
export { validateConfig } from "./config/parser"

/**
 * Define verification configuration
 * This is a helper function that provides type checking for the config
 */
export function defineVerification(config: any): any {
  return config
}

// Verification primitives (requires, ensures, invariant)
export * from "./primitives/index"
