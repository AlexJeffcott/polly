/**
 * @fairfox/polly/quality — conformance checks for Polly applications.
 *
 * Exports the same quality rules that Polly enforces on itself, so
 * consuming applications can adopt the same standards. The flagship
 * check is `isLineClean` which detects forbidden `as` type assertions;
 * applications wire it into their own CI or pre-commit hook via the
 * companion `checkNoAsCasting` runner.
 *
 * The CSS conformance family — `checkCssQuality`, `checkCssLayout`,
 * `checkCssVars`, `checkCssUnused` — enforces the token-driven styling
 * contract that @fairfox/polly/ui ships: all styled values go through
 * semantic tokens, layout goes through the `<Layout>` primitive, no
 * variable references dangle, and unused selectors are surfaced.
 *
 * @example
 * ```typescript
 * import { checkNoAsCasting } from "@fairfox/polly/quality";
 *
 * const result = await checkNoAsCasting({
 *   rootDir: process.cwd(),
 *   exclude: ["node_modules", "dist"],
 * });
 *
 * if (result.violations.length > 0) {
 *   result.print();
 *   process.exit(1);
 * }
 * ```
 */

export {
  type CssLayoutOptions,
  checkCssLayout,
} from "./css/check-layout.ts";

export {
  type CssQualityOptions,
  checkCssQuality,
} from "./css/check-quality.ts";
export { type CssUnusedOptions, checkCssUnused } from "./css/check-unused.ts";
export { type CssVarsOptions, checkCssVars } from "./css/check-vars.ts";
export type { CssCheckResult, CssViolation } from "./css/shared.ts";
export {
  logger,
  type QualityLogger,
  resetLogger,
} from "./logger.ts";
export {
  type CheckResult,
  checkNoAsCasting,
  isLineClean,
  suggestFix,
  type Violation,
} from "./no-as-casting";
