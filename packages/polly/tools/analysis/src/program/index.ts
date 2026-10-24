// typescript-7 program and AST helpers for the static-analysis extractors.
// See analysis-program.ts for the session lifecycle (close() is mandatory).

export {
  AnalysisProgram,
  AnalysisSession,
  type AnalysisSource,
  isDefinitionSite,
  MORPH_TYPE_FORMAT,
  type PropertyInfo,
  withAnalysisSession,
  withProgram,
} from "./analysis-program";
export {
  declarationKind,
  firstAncestor,
  firstDescendant,
  forEachDescendant,
  functionDeclaration,
  functionDeclarations,
  hasExportKeyword,
  importDeclarations,
  importedName,
  isJSDocable,
  jsDocDescription,
  jsDocs,
  jsDocText,
  kindName,
  leadingComments,
  lineAndColumn,
  literalValue,
  moduleSpecifierValue,
  namedImports,
  nameOf,
  objectProperty,
  startLine,
  startLinePos,
  startOf,
  textOf,
  typeAlias,
  typeAliases,
  variableDeclaration,
  variableStatements,
} from "./ast";
export { createSourceGlob } from "./glob";
export { typeIs, typeLiteralValue } from "./type-flags";
