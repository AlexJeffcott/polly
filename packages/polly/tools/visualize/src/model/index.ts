// The @fairfox/polly/visualize library surface: a declared C4 model, its
// checker and its DSL writer. A `--model` file imports its types from here.

export { DeclaredModelError, readDeclaredModel } from "./check";
export { type DeclaredModelFragment, declaredModelDSL, declaredModelFragment } from "./dsl";
export type * from "./types";
