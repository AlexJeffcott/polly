/**
 * @fairfox/polly/test/visual — visual regression harness.
 *
 * Wraps the existing Puppeteer browser harness with screenshot capture
 * and baseline diffing via pixelmatch. Consumer tests call
 * `matchBaseline(page, name, baselinesDir, diffsDir)` on an already-
 * rendered page; the result carries pass/fail plus the diff PNG path.
 *
 *   import { matchBaseline, resolveVisualPaths } from "@fairfox/polly/test/visual";
 */

export {
  compareImages,
  type VisualCompareOptions,
  type VisualCompareResult,
} from "./compare.ts";
export {
  assertSafeUpdateMode,
  isCi,
  isUpdateMode,
  matchBaseline,
  resolveVisualPaths,
  type VisualMatchFailure,
  type VisualMatchOptions,
  type VisualMatchResult,
  type VisualMatchSuccess,
} from "./harness.ts";
