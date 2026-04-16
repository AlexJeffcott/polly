/**
 * @fairfox/polly/quality — conformance checks for Polly applications.
 *
 * Exports the same quality rules that Polly enforces on itself, so
 * consuming applications can adopt the same standards. The flagship
 * check is `isLineClean` which detects forbidden `as` type assertions;
 * applications wire it into their own CI or pre-commit hook via the
 * companion `checkNoAsCasting` runner.
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
  type CheckResult,
  checkNoAsCasting,
  isLineClean,
  suggestFix,
  type Violation,
} from "./no-as-casting";
