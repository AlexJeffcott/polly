// Export all core types
export * from "./core";

// Export architecture types
export * from "./architecture";

// Export ADR types
export * from "./adr";

// Extension-specific context types
export type Context =
  | "background"
  | "content"
  | "popup"
  | "devtools"
  | "options"
  | "offscreen"
  | "sidepanel";
