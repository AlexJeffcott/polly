// Tests demonstrating framework double-execution prevention.
// These are documentation tests that explain the framework's protection mechanisms.

import { describe, expect, test } from "bun:test";

/*
 * Singleton pattern.
 *
 * The framework enforces that only ONE MessageRouter can exist. Calling
 * createBackground() twice triggers the guard:
 *
 *     const bus1 = createBackground()  // OK
 *     const bus2 = createBackground()  // ERROR!
 *
 * The guard prints:
 *
 *     MessageRouter already exists!
 *     Only ONE MessageRouter can exist in the background context.
 *     Multiple MessageRouter instances will cause handlers to execute
 *     multiple times.
 *
 * This prevents accidentally calling createBackground() twice.
 */
describe("Framework Double-Execution Prevention (Documentation)", () => {
  test("documents the singleton pattern", () => {
    expect(true).toBe(true);
  });

  /*
   * Why createBackground() is needed.
   *
   * CORRECT — use createBackground() in background scripts:
   *
   *     const bus = createBackground()
   *
   * This does:
   *   1. Creates MessageBus WITHOUT chrome.runtime.onMessage listener.
   *   2. Creates MessageRouter WITH chrome.runtime.onMessage listener.
   *   3. Result: only ONE listener total, no double execution.
   *
   * WRONG — don't do this:
   *
   *     const bus = getMessageBus('background')
   *     new MessageRouter(bus)
   *
   * This creates:
   *   1. MessageBus WITH chrome.runtime.onMessage listener.
   *   2. MessageRouter WITH chrome.runtime.onMessage listener.
   *   3. Result: TWO listeners, double-execution bug.
   */
  test("documents why createBackground() is needed", () => {
    expect(true).toBe(true);
  });

  /*
   * What NOT to do.
   *
   * WRONG in background scripts:
   *
   *     const bus = getMessageBus('background')
   *     new MessageRouter(bus)
   *
   * This creates TWO chrome.runtime.onMessage listeners:
   *   1. MessageBus's listener (from its constructor).
   *   2. MessageRouter's listener (from MessageRouter's constructor).
   *
   * Result: every handler executes TWICE for every message.
   *
   * The framework now prevents this with:
   *   - Singleton MessageRouter (throws if created twice).
   *   - Listener count warning (warns if multiple listeners).
   *   - Execution tracker (throws on double execution in dev mode).
   */
  test("documents what NOT to do", () => {});
});

/*
 * Execution tracker in development.
 *
 * If a handler somehow executes twice for the same message, the tracker
 * prints:
 *
 *     DOUBLE EXECUTION DETECTED
 *
 *     Handler "TODO_ADD" executed 2 times for message abc-123.
 *
 *     This indicates multiple chrome.runtime.onMessage listeners are
 *     registered. Common causes:
 *       1. Both MessageBus and MessageRouter registered listeners.
 *       2. createBackground() called multiple times.
 *       3. Handler registered in multiple places.
 *
 *     Fix: ensure only ONE listener is registered. In background scripts,
 *     use createBackground() instead of getMessageBus(). The tracker is
 *     automatically enabled in development mode — no setup needed.
 */
describe("Example: Handler Execution in Development", () => {
  test("execution tracker would catch double execution", () => {});
});
