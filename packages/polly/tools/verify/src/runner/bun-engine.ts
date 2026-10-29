/**
 * `verification.engine: "bun"` / `--engine bun`: the safety pass on polly's
 * own checker (checker/check.ts) instead of TLC in Docker. Its result has the
 * shape of a TLC run, so the report, the handler-coverage reading and the
 * exit code are the ones a TLC run gets.
 */

import path from "node:path";
import { type CheckCounts, type CheckResult, checkSpec } from "../checker/check";
import type { TLCResult, TLCStats } from "./docker";

export type VerifyEngine = "tlc" | "bun";

export type BunRun =
  | {
      kind: "result";
      result: TLCResult;
      /** Times each handler action was taken; only for a completed run. */
      handlerCounts?: Map<string, number>;
      /** cfg PROPERTIES the checker did not check. */
      properties: string[];
    }
  | { kind: "unsupported"; reason: string };

function stats(c: CheckCounts, exhaustive: boolean): TLCStats {
  return {
    statesGenerated: c.generated,
    distinctStates: c.distinct,
    statesLeftOnQueue: exhaustive ? 0 : Math.max(1, c.leftOnQueue),
    initialStates: c.initial,
    searchDepth: c.depth,
    exhaustive,
    noActionEnabled: c.distinct === c.initial,
  };
}

/** The run as text, for `tlc-output.log`: TLC's summary lines, so a reader of the log finds them. */
function outputText(r: Exclude<CheckResult, { kind: "unsupported" }>): string {
  const c = r.counts;
  const lines = [`polly Bun checker (safety only), ${r.seconds.toFixed(2)} s`];
  if (r.kind === "violation") {
    lines.push(
      r.what === "deadlock"
        ? "Error: Deadlock reached."
        : `Error: Invariant ${r.name} is violated.`,
      "Error: The behavior up to this point is:",
      ...r.trace
    );
  }
  if (r.kind === "timeout") lines.push("Stopped at the timeout.");
  lines.push(
    `Finished computing initial states: ${c.initial} distinct states generated.`,
    `${c.generated} states generated, ${c.distinct} distinct states found, ${c.leftOnQueue} states left on queue.`,
    `The depth of the complete state graph search is ${c.depth}.`
  );
  if (r.properties.length > 0) lines.push(`PROPERTIES not checked: ${r.properties.join(", ")}`);
  return `${lines.join("\n")}\n`;
}

export function runBunChecker(specPath: string, opts: { timeoutMs?: number }): BunRun {
  const r = checkSpec({
    specDir: path.dirname(specPath),
    moduleName: path.basename(specPath, ".tla"),
    ...(opts.timeoutMs === undefined ? {} : { timeoutMs: opts.timeoutMs }),
  });
  if (r.kind === "unsupported") return r;
  const output = outputText(r);
  switch (r.kind) {
    case "done":
      return {
        kind: "result",
        result: { success: true, stats: stats(r.counts, true), output },
        handlerCounts: r.handlerCounts,
        properties: r.properties,
      };
    case "violation":
      return {
        kind: "result",
        result: {
          success: false,
          violation: {
            type: r.what,
            ...(r.name === undefined ? {} : { name: r.name }),
            trace: r.trace,
          },
          stats: stats(r.counts, false),
          output,
        },
        properties: r.properties,
      };
    case "timeout":
      return {
        kind: "result",
        result: {
          success: false,
          error: `the Bun checker stopped at the timeout after ${r.counts.distinct} distinct states, with ${r.counts.leftOnQueue} not yet expanded`,
          stats: stats(r.counts, false),
          output,
        },
        properties: r.properties,
      };
  }
}
