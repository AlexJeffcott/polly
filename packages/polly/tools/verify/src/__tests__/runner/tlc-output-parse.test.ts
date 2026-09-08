import { describe, expect, test } from "bun:test";
import { parseTLCStats } from "../../runner/docker";

/**
 * polly#182: the state count polly reports.
 *
 * TLC prints two lines containing the substring `distinct states`. The parse
 * used `output.match(/(\d+) distinct states/)` — non-global, so the first hit —
 * and the initial-states line always comes first. Every run therefore reported
 * its INITIAL-state count as its distinct-state count: three subsystems that
 * explored 116,032 / 29,248 / 97,600 states all printed `8 states  ✓ passed`,
 * and so would a spec in which no action was ever enabled.
 *
 * These transcripts are TLC 2.19's real output, from the polly-tla image.
 */

/** A completed, exhaustive run: eal's `auth` subsystem at 7 handlers. */
const EXHAUSTIVE_RUN = `TLC2 Version 2.19 of Day Month 20?? (rev: 6fbfa2c)
Running breadth-first search Model-Checking with fp 82 and seed -6409953662600935953 with 1 worker on 6 cores with 6000MB heap and 64MB offheap memory
Parsing file /work/UserApp_auth.tla
Starting... (2026-09-08 13:00:51)
Computing initial states...
Finished computing initial states: 8 distinct states generated at 2026-09-08 13:00:52.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.0E-9
  based on the actual fingerprints:  val = 8.2E-10
477320 states generated, 97600 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 9.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 31 and the 95th percentile is 2).
Finished in 01s at (2026-09-08 13:00:52)
`;

/** A `-depth`-bounded run: TLC prints a summary but the graph is truncated. */
const BOUNDED_RUN = `Finished computing initial states: 8 distinct states generated at 2026-09-08 13:00:52.
Model checking completed. No error has been found.
9622903 states generated, 4811451 distinct states found, 8009447 states left on queue.
The depth of the complete state graph search is 6.
`;

/** A killed run: progress lines, no summary line at all. */
const KILLED_RUN = `Finished computing initial states: 8 distinct states generated at 2026-09-08 13:00:52.
Progress(5) at 2026-09-08 13:03:11: 4818421 states generated (1,010,441 s/min), 2404118 distinct states found (503,880 ds/min), 2001328 states left on queue.
`;

/**
 * A killed run whose last line is TLC's FIRST progress report. The rate
 * suffixes are empty there, so the line reads exactly like a summary line —
 * except for the `Progress(N) at <time>:` prefix.
 */
const KILLED_ON_FIRST_PROGRESS = `Finished computing initial states: 8 distinct states generated at 2026-09-08 13:00:52.
Progress(0) at 2026-09-08 13:00:52: 8 states generated, 8 distinct states found, 0 states left on queue.
`;

/** A model in which no handler is ever enabled: exhausted at its initial states. */
const NO_ACTION_ENABLED = `Finished computing initial states: 8 distinct states generated at 2026-09-08 13:00:52.
Model checking completed. No error has been found.
8 states generated, 8 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 1.
`;

describe("parseTLCStats", () => {
  test("reads the distinct-state count from the summary line, not the initial-states line", () => {
    const parsed = parseTLCStats(EXHAUSTIVE_RUN);

    expect(parsed?.stats.distinctStates).toBe(97_600);
    expect(parsed?.stats.statesGenerated).toBe(477_320);
    // The number the old parse returned. It must not be the answer.
    expect(parsed?.stats.distinctStates).not.toBe(8);
  });

  test("keeps the initial-state count in its own field", () => {
    expect(parseTLCStats(EXHAUSTIVE_RUN)?.stats.initialStates).toBe(8);
  });

  test("captures the queue remainder and the search depth", () => {
    const stats = parseTLCStats(EXHAUSTIVE_RUN)?.stats;

    expect(stats?.statesLeftOnQueue).toBe(0);
    expect(stats?.searchDepth).toBe(9);
    expect(stats?.exhaustive).toBe(true);
  });

  test("a non-zero queue is not an exhausted model", () => {
    const stats = parseTLCStats(BOUNDED_RUN)?.stats;

    expect(stats?.distinctStates).toBe(4_811_451);
    expect(stats?.statesLeftOnQueue).toBe(8_009_447);
    expect(stats?.exhaustive).toBe(false);
  });

  test("a run with no summary line reports nothing, not zero and not the initial count", () => {
    expect(parseTLCStats(KILLED_RUN)).toBeUndefined();
  });

  test("an empty transcript reports nothing", () => {
    expect(parseTLCStats("")).toBeUndefined();
  });

  test("a model where no action fires is flagged, however exhaustively it was explored", () => {
    const stats = parseTLCStats(NO_ACTION_ENABLED)?.stats;

    expect(stats?.distinctStates).toBe(8);
    expect(stats?.exhaustive).toBe(true);
    expect(stats?.noActionEnabled).toBe(true);
  });

  test("a model with genuine transitions is not flagged", () => {
    expect(parseTLCStats(EXHAUSTIVE_RUN)?.stats.noActionEnabled).toBe(false);
  });

  test("a rate-less first progress line is not mistaken for the summary line", () => {
    // The one progress line that is word-for-word a summary line. Only the
    // `Progress(0) at <time>:` prefix separates them, which is why the pattern
    // is anchored to the start of a line.
    expect(parseTLCStats(KILLED_ON_FIRST_PROGRESS)).toBeUndefined();
  });
});
