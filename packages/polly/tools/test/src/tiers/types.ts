/**
 * Manifest types for the tiered test engine.
 *
 * The engine is deliberately pure: it knows how to *run* a plan of cases as
 * isolated subprocesses, gate them on environment capabilities, time them, and
 * report. It knows nothing about Polly's specific scripts — those are supplied
 * as a {@link TierPlan} by a front-end (Polly's internal registry, or a
 * consumer-discovery step behind `polly test`). This keeps the engine reusable
 * and respects the repo's src → tools → cli → scripts import boundary.
 */

/** A capability a case needs from the host before it can run. */
export type Need = "docker" | "browser" | "network";

/** How a case is executed. Both forms run in their own subprocess. */
export type CaseExec =
  | {
      /**
       * A module that may `export async function run(ctx)`. The worker imports
       * it; if `run` is exported it is called for a structured result,
       * otherwise the module's import side-effect (legacy top-level `main()`)
       * runs and its `process.exitCode` becomes the result. This is what lets
       * converted and unconverted scripts coexist.
       */
      kind: "module";
      modulePath: string;
    }
  | {
      /** An arbitrary command; success is exit code 0. */
      kind: "command";
      argv: string[];
      cwd?: string;
    };

/** One runnable unit within a tier. */
export interface CaseSpec {
  /** Stable id, e.g. "mesh.blob-transfer". Used for --only matching. */
  id: string;
  /** Human label for reports; defaults to id. */
  label?: string;
  /** Free-form tags for --only filtering (e.g. "mesh", "revocation"). */
  tags?: string[];
  /** Host capabilities required; unmet → skipped with a logged reason. */
  needs?: Need[];
  /** Per-case timeout. Defaults to the engine's tier default. */
  timeoutMs?: number;
  /**
   * Coarse cost hint consumed by `--order` (see order.ts). Unset = "medium".
   * A scheduling hint, not a measurement — tune from `--json` durations.
   */
  cost?: "light" | "medium" | "heavy";
  exec: CaseExec;
}

/** An ordered group of cases sharing a realism level. */
export interface Tier {
  name: string;
  /** One-line description shown by --list. */
  description?: string;
  /** Run cases in this tier concurrently up to this many at once. Default 1. */
  concurrency?: number;
  /** Default per-case timeout for this tier. */
  timeoutMs?: number;
  cases: CaseSpec[];
}

/** The full thing handed to the engine. Tiers run in array order. */
export interface TierPlan {
  tiers: Tier[];
}

export type CaseOutcome = "pass" | "fail" | "skip" | "timeout";

/** How cases are ordered within a tier before the pool drains them. */
export type CaseOrder = "default" | "fast" | "cost";

export interface CaseReport {
  tier: string;
  id: string;
  label: string;
  outcome: CaseOutcome;
  durationMs: number;
  message?: string;
  /** Reason a case was skipped (unmet need). */
  skipReason?: string;
}

export interface RunReport {
  cases: CaseReport[];
  passed: number;
  failed: number;
  skipped: number;
  durationMs: number;
  ok: boolean;
}

/** Options controlling a single engine run. */
export interface EngineOptions {
  /** Only run these tiers (by name). Empty = all tiers in the plan. */
  tiers?: string[];
  /** Only run cases whose id/label/tags match one of these substrings. */
  only?: string[];
  /** Order cases within each tier. Default "default" (definition order). */
  order?: CaseOrder;
  /** Stop after the first tier that has a failure. */
  bail?: boolean;
  /**
   * Soft fail-fast: on the first failing case, the tier's pool stops *claiming*
   * new cases (in-flight ones finish) and the run stops after that tier. Unlike
   * `bail`, which lets every case in the failing tier finish first.
   */
  failFast?: boolean;
  /** Treat unmet-need skips as failures (CI-strict). Default false. */
  strictNeeds?: boolean;
  /** Forwarded into each case's environment. */
  env?: Record<string, string | undefined>;
  /** Default working directory for cases that don't set their own. */
  cwd?: string;
  /** Sink for engine-level progress lines. Defaults to console.log. */
  log?: (message: string) => void;
}
