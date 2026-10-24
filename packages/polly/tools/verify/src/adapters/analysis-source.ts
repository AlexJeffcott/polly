// Where an adapter gets its typescript-7 program from.
//
// A caller that already runs an AnalysisSession passes it (or a program
// opened from it) and keeps ownership: the adapter never closes it. With
// nothing passed, the adapter opens a session of its own for the one call
// and closes it before returning, so no tsgo process outlives the call.

import {
  AnalysisProgram,
  AnalysisSession,
  withAnalysisSession,
} from "../../../analysis/src/program";

/** A session (the adapter opens its tsconfig in it) or an already-open program. */
export type AnalysisSource = AnalysisSession | AnalysisProgram;

/**
 * Run `fn` on the program for `tsConfigPath`: the given program as is, the
 * project opened in the given session, or a session of its own, closed
 * however `fn` ends.
 */
export async function withAdapterProgram<T>(
  tsConfigPath: string,
  source: AnalysisSource | undefined,
  fn: (program: AnalysisProgram) => T | Promise<T>
): Promise<T> {
  if (source instanceof AnalysisProgram) return fn(source);
  if (source instanceof AnalysisSession) return fn(await source.open(tsConfigPath));
  return withAnalysisSession(async (session) => fn(await session.open(tsConfigPath)));
}
