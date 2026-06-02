/**
 * Tests for handler-execution-tracker.ts — the dev-mode guard that detects a
 * handler running more than once for the same message id (the symptom of a
 * duplicate chrome.runtime.onMessage listener).
 *
 * Two things need controlling to make the logic observable:
 *
 *  - `isDevelopment` is captured in the constructor from `process.env.NODE_ENV`,
 *    so each test sets NODE_ENV before constructing and restores it after.
 *  - `track()` schedules a real 5s `setTimeout` for cleanup; the global is
 *    stubbed so the scheduled callback (and its 5000ms delay) can be asserted
 *    and fired synchronously instead of leaking a timer.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { HandlerExecutionTracker } from "@/shared/lib/handler-execution-tracker";

// ---------------------------------------------------------------------------
// NODE_ENV control — isDevelopment is read once, at construction time.
// ---------------------------------------------------------------------------

let savedNodeEnv: string | undefined;

beforeEach(() => {
  savedNodeEnv = process.env.NODE_ENV;
});

afterEach(() => {
  if (savedNodeEnv === undefined) delete process.env.NODE_ENV;
  else process.env.NODE_ENV = savedNodeEnv;
});

/** Construct a tracker under a chosen NODE_ENV. */
function trackerWithEnv(nodeEnv: string | undefined): HandlerExecutionTracker {
  if (nodeEnv === undefined) delete process.env.NODE_ENV;
  else process.env.NODE_ENV = nodeEnv;
  return new HandlerExecutionTracker();
}

// ---------------------------------------------------------------------------
// setTimeout stub — capture cleanup schedules without waiting 5s.
// ---------------------------------------------------------------------------

interface TimerCall {
  fn: () => void;
  ms: number;
}

let timers: TimerCall[];
const realSetTimeout = globalThis.setTimeout;

function stubSetTimeout(): void {
  timers = [];
  (globalThis as unknown as { setTimeout: unknown }).setTimeout = ((fn: () => void, ms: number) => {
    timers.push({ fn, ms });
    return 0;
  }) as unknown as typeof setTimeout;
}

function restoreSetTimeout(): void {
  (globalThis as unknown as { setTimeout: typeof setTimeout }).setTimeout = realSetTimeout;
}

// ---------------------------------------------------------------------------
// Development-mode gate
// ---------------------------------------------------------------------------

describe("isDevelopment gate", () => {
  beforeEach(stubSetTimeout);
  afterEach(restoreSetTimeout);

  test("tracks when NODE_ENV is development", () => {
    const tracker = trackerWithEnv("development");
    tracker.track("m1", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
  });

  test("tracks when NODE_ENV is test", () => {
    const tracker = trackerWithEnv("test");
    tracker.track("m1", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
  });

  test("is a no-op when NODE_ENV is production", () => {
    const tracker = trackerWithEnv("production");
    tracker.track("m1", "H");
    tracker.track("m1", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(0);
    // No throw on the second call either, because tracking is disabled.
    expect(timers).toHaveLength(0);
  });

  test("is a no-op when NODE_ENV is unset", () => {
    const tracker = trackerWithEnv(undefined);
    tracker.track("m1", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(0);
  });
});

// ---------------------------------------------------------------------------
// track() — counting, lazy map init, and the double-execution throw
// ---------------------------------------------------------------------------

describe("track", () => {
  let tracker: HandlerExecutionTracker;

  beforeEach(() => {
    stubSetTimeout();
    tracker = trackerWithEnv("test");
  });
  afterEach(restoreSetTimeout);

  test("a single execution counts as exactly 1 and does not throw", () => {
    expect(() => tracker.track("m1", "H")).not.toThrow();
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
  });

  test("counts repeated handler types independently per message", () => {
    tracker.track("m1", "A");
    tracker.track("m1", "B");
    expect(tracker.getExecutionCount("m1", "A")).toBe(1);
    expect(tracker.getExecutionCount("m1", "B")).toBe(1);
  });

  test("the same handler under two different messages stays at 1 each", () => {
    tracker.track("m1", "H");
    tracker.track("m2", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
    expect(tracker.getExecutionCount("m2", "H")).toBe(1);
  });

  test("a second execution of the same handler+message throws", () => {
    tracker.track("m1", "H");
    expect(() => tracker.track("m1", "H")).toThrow();
  });

  test("the thrown error names the handler, the count, and the message", () => {
    tracker.track("dup-msg", "DUP_HANDLER");
    expect(() => tracker.track("dup-msg", "DUP_HANDLER")).toThrow(/DOUBLE EXECUTION/);
    try {
      tracker.track("dup-msg", "DUP_HANDLER");
    } catch (err) {
      const message = (err as Error).message;
      expect(message).toContain("DUP_HANDLER");
      expect(message).toContain("dup-msg");
      // Count is 3 by this third call — the message interpolates it.
      expect(message).toContain("3 times");
    }
  });

  test("schedules a 5s cleanup that removes the message's executions", () => {
    tracker.track("m1", "H");
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
    // Exactly one cleanup timer, scheduled at 5000ms.
    expect(timers).toHaveLength(1);
    expect(timers[0]!.ms).toBe(5000);
    // Firing it clears the message's tracked executions.
    timers[0]!.fn();
    expect(tracker.getExecutionCount("m1", "H")).toBe(0);
  });

  test("does not schedule a cleanup once the double-execution throw fires", () => {
    tracker.track("m1", "H"); // schedules one timer
    expect(() => tracker.track("m1", "H")).toThrow(); // throws before scheduling
    expect(timers).toHaveLength(1);
  });

  test("logs the execution trace, labelled, before throwing", () => {
    const realError = console.error;
    const errorCalls: unknown[][] = [];
    console.error = (...args: unknown[]) => errorCalls.push(args);
    try {
      tracker.track("m1", "H");
      expect(() => tracker.track("m1", "H")).toThrow();
    } finally {
      console.error = realError;
    }
    // One of the console.error calls carries the labelled trace.
    expect(errorCalls.some((c) => c[0] === "Execution trace for message:" && c[1] === "m1")).toBe(
      true
    );
  });
});

// ---------------------------------------------------------------------------
// reset / getExecutionCount
// ---------------------------------------------------------------------------

describe("reset and getExecutionCount", () => {
  beforeEach(stubSetTimeout);
  afterEach(restoreSetTimeout);

  test("getExecutionCount returns 0 for an untracked message", () => {
    const tracker = trackerWithEnv("test");
    expect(tracker.getExecutionCount("never", "H")).toBe(0);
  });

  test("getExecutionCount returns 0 for a known message but unknown handler", () => {
    const tracker = trackerWithEnv("test");
    tracker.track("m1", "A");
    expect(tracker.getExecutionCount("m1", "B")).toBe(0);
  });

  test("reset clears all tracked executions", () => {
    const tracker = trackerWithEnv("test");
    tracker.track("m1", "H");
    tracker.track("m2", "H");
    tracker.reset();
    expect(tracker.getExecutionCount("m1", "H")).toBe(0);
    expect(tracker.getExecutionCount("m2", "H")).toBe(0);
  });

  test("after reset a previously-tracked handler can run again without throwing", () => {
    const tracker = trackerWithEnv("test");
    tracker.track("m1", "H");
    tracker.reset();
    expect(() => tracker.track("m1", "H")).not.toThrow();
    expect(tracker.getExecutionCount("m1", "H")).toBe(1);
  });
});
