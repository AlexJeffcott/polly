/**
 * @fairfox/polly/test/coverage — the per-file coverage policy a consumer can
 * declare. Every field is optional so the tool runs zero-config: with no
 * `coverage.config.ts` the enforcer reports numbers and orphans without
 * failing; add a `defaultThreshold` to start enforcing, and `exempt` entries
 * to record which higher-tier test covers a unit-thin file.
 */

export interface FileThreshold {
  /** Minimum `% Lines` from the `bun test --coverage` table. */
  lines: number;
  /** Minimum `% Funcs` from the `bun test --coverage` table. */
  funcs: number;
}

export interface ExemptEntry {
  /** Why this file is thin at the unit tier. */
  reason: string;
  /**
   * Package-relative path to the test or script that exercises this file at a
   * higher tier. Verified to exist by the enforcer. Use the `'n/a — <reason>'`
   * form for genuine waivers (extension-only shims, browser-only geometry).
   */
  claimedBy: string;
}

export interface CoverageConfig {
  /** Per-file floor. Omit to run report-only (numbers + orphans, never fails). */
  defaultThreshold?: FileThreshold;
  /** Files below the floor that are covered at a higher tier, keyed by
   *  source path relative to the project root (e.g. `src/shared/lib/x.ts`). */
  exempt?: Record<string, ExemptEntry>;
  /** Source directory to police, relative to the project root. Default `src`. */
  srcDir?: string;
  /** Directory to run `bun test --coverage` in, relative to the project root.
   *  Default `.` (the root). Polly itself runs its suite from `tests`. */
  testCwd?: string;
}
