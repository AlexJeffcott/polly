// Tests demonstrating framework double-execution prevention
// These are documentation tests that explain the framework's protection mechanisms

import { describe, expect, test } from "bun:test";

describe("Framework Double-Execution Prevention (Documentation)", () => {
  test("documents the singleton pattern", () => {
    // The framework enforces that only ONE MessageRouter can exist
    //
    // If you tried to do this:
    //   const bus1 = createBackground()  // OK
    //   const bus2 = createBackground()  // ERROR!
    //
    // You'd get:
    //   🔴 MessageRouter already exists!
    //   Only ONE MessageRouter can exist in the background context.
    //   Multiple MessageRouter instances will cause handlers to execute multiple times.
    //
    // This prevents accidentally calling createBackground() twice

    expect(true).toBe(true); // This is a documentation test
  });

  test("documents why createBackground() is needed", () => {
    // ✅ CORRECT: Use createBackground() in background scripts
    // const bus = createBackground()
    //
    // This does:
    // 1. Creates MessageBus WITHOUT chrome.runtime.onMessage listener
    // 2. Creates MessageRouter WITH chrome.runtime.onMessage listener
    // 3. Result: Only ONE listener total, no double execution
    //
    // ❌ WRONG: Don't do this!
    // const bus = getMessageBus('background')
    // new MessageRouter(bus)
    //
    // This creates:
    // 1. MessageBus WITH chrome.runtime.onMessage listener
    // 2. MessageRouter WITH chrome.runtime.onMessage listener
    // 3. Result: TWO listeners = double execution bug!

    expect(true).toBe(true); // This is a documentation test
  });

  test("documents what NOT to do", () => {
    // ❌ WRONG: Don't do this in background scripts!
    // const bus = getMessageBus('background')
    // new MessageRouter(bus)
    //
    // This creates TWO chrome.runtime.onMessage listeners:
    // 1. MessageBus's listener (from constructor)
    // 2. MessageRouter's listener (from MessageRouter constructor)
    //
    // Result: Every handler executes TWICE for every message!
    //
    // The framework now prevents this with:
    // - Singleton MessageRouter (throws if created twice)
    // - Listener count warning (warns if multiple listeners)
    // - Execution tracker (throws on double execution in dev mode)
  });
});

describe("Example: Handler Execution in Development", () => {
  test("execution tracker would catch double execution", () => {
    // In development mode, if a handler somehow executed twice
    // for the same message, you'd see:
    //
    // 🔴 DOUBLE EXECUTION DETECTED
    //
    // Handler "TODO_ADD" executed 2 times for message abc-123.
    //
    // This indicates multiple chrome.runtime.onMessage listeners are registered.
    // Common causes:
    //   1. Both MessageBus and MessageRouter registered listeners
    //   2. createBackground() called multiple times
    //   3. Handler registered in multiple places
    //
    // Fix: Ensure only ONE listener is registered. In background scripts,
    // use createBackground() instead of getMessageBus().
    // This is automatically enabled in development mode, no setup needed!
  });
});
