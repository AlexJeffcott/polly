// Export all core types

// Export ADR types
export * from "./adr";

// Export architecture types
export * from "./architecture";
export * from "./core";

// Extension-specific context types
export type Context =
  | "background"
  | "content"
  | "popup"
  | "devtools"
  | "options"
  | "offscreen"
  | "sidepanel";
