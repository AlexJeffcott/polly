// Public API for @fairfox/web-ext-verify

export type { VerificationConfig, ValidationResult, CodebaseAnalysis } from "./types"

export { analyzeCodebase } from "./extract/types"
export { generateConfig } from "./codegen/config"
export { validateConfig } from "./config/parser"

/**
 * Define verification configuration
 * This is a helper function that provides type checking for the config
 */
export function defineVerification(config: any): any {
  return config
}

// Re-export primitive API (TODO: implement)
export * from "./primitives/index"
