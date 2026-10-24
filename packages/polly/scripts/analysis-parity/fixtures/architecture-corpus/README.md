Corpus project for `scripts/analysis-parity.ts`. It exists to exercise the
architecture extractors (`ContextAnalyzer`, `FlowAnalyzer`,
`IntegrationAnalyzer`) and handler relationships on the shapes the example
workspaces never reach: UI components (function, arrow, class, mapped-type
props, multi-line JSDoc), chrome/browser/bus.adapters API use, file-level
descriptions, `@flow`/`@trigger` sender annotations, fetch and WebSocket
integrations, scoped and `bun` imports, and cross-file function calls.
Change it and the golden must be re-recorded.
