// Deterministic source-file order for the ts-morph extractors.
//
// ts-morph's getSourceFiles() returns files in its own internal order
// (directory insertion order), which the TypeScript 7 API cannot reproduce.
// Every extractor that iterates the project's files does so in absolute-path
// order instead, so output order no longer depends on the compiler host.

import type { Project, SourceFile } from "ts-morph";

/** Plain code-unit comparison of absolute file paths (not locale-aware). */
export function compareFilePaths(a: string, b: string): number {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

/** `project.getSourceFiles(glob?)`, sorted by absolute file path. */
export function sourceFilesInPathOrder(project: Project, glob?: string): SourceFile[] {
  const files = glob === undefined ? project.getSourceFiles() : project.getSourceFiles(glob);
  return [...files].sort((a, b) => compareFilePaths(a.getFilePath(), b.getFilePath()));
}
