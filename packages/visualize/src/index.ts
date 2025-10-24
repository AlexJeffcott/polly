// Main entry point for @fairfox/web-ext-visualize

// Export DSL generator
export * from "./codegen/structurizr"

// Export diagram exporter
export * from "./runner/export"

// Export interactive viewer
export * from "./viewer/server"

// Re-export analysis functionality for convenience
export { analyzeArchitecture, type ArchitectureAnalysis } from "@fairfox/web-ext-analysis"
