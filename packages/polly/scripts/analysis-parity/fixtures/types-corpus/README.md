Corpus project for `scripts/analysis-parity.ts`. It exists to exercise the
type-driven extractors (`TypeExtractor.convertType`, `findMessageTypes`)
that the example workspaces barely reach: `polly verify` finds a state type
only at `src/types/state.ts`, and message types only in `**/message*.ts`.
Change it and the golden must be re-recorded.
