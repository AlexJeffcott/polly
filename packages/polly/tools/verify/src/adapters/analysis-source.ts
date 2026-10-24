// Where an adapter gets its typescript-7 program from.
//
// A caller that already runs an AnalysisSession passes it (or a program
// opened from it) and keeps ownership: the adapter never closes it. With
// nothing passed, the adapter opens a session of its own for the one call
// and closes it before returning, so no tsgo process outlives the call.
// The implementation is shared with the extractors (program module).

export {
  type AnalysisSource,
  withProgram as withAdapterProgram,
} from "../../../analysis/src/program";
