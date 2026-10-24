Corpus project for `scripts/analysis-parity.ts`. It exists to exercise the
`HandlerExtractor` lookups the example workspaces barely reach: handler
references resolved through go-to-definition (imported, aliased, re-exported,
`const` arrow and function expression, overloaded, destructured from a dynamic
import), handler-map values, imported type guards (declaration, arrow, alias
re-export, body-only, `asserts`, ambient, default-library), initial-state
fields read through an identifier (local and imported), and the issue-#27 lift
of mutators exported by `export { f }`, `export { f as g }` and
`export default f` as well as by keyword. Change it and the golden must be
re-recorded.
