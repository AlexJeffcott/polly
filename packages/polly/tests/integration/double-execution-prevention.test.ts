// Integration test to prevent double-execution bugs
// This test would have caught the MessageBus + MessageRouter double listener issue

import { beforeEach, describe, expect, test } from "bun:test";
import { globalExecutionTracker } from "../../src/shared/lib/handler-execution-tracker";

describe("Double Execution Prevention", () => {
  beforeEach(() => {
    globalExecutionTracker.reset();
  });

  test("handler execution tracker detects double execution", () => {
    const messageId = "test-message-1";
    const handlerType = "TEST_HANDLER";

    // First execution should succeed
    expect(() => {
      globalExecutionTracker.track(messageId, handlerType);
    }).not.toThrow();

    // Second execution should throw
    expect(() => {
      globalExecutionTracker.track(messageId, handlerType);
    }).toThrow(/DOUBLE EXECUTION DETECTED/);
  });

  test("different message IDs are tracked independently", () => {
    const handlerType = "TEST_HANDLER";

    // Multiple different messages should all succeed
    expect(() => {
      globalExecutionTracker.track("message-1", handlerType);
      globalExecutionTracker.track("message-2", handlerType);
      globalExecutionTracker.track("message-3", handlerType);
    }).not.toThrow();

    // But same message ID twice should fail
    expect(() => {
      globalExecutionTracker.track("message-1", handlerType);
    }).toThrow();
  });

  test("different handler types for same message are tracked independently", () => {
    const messageId = "test-message-1";

    // Different handlers for same message should succeed
    expect(() => {
      globalExecutionTracker.track(messageId, "HANDLER_A");
      globalExecutionTracker.track(messageId, "HANDLER_B");
    }).not.toThrow();

    // But same handler twice should fail
    expect(() => {
      globalExecutionTracker.track(messageId, "HANDLER_A");
    }).toThrow();
  });

  test("execution count is tracked correctly", () => {
    const messageId = "test-message-1";
    const handlerType = "TEST_HANDLER";

    expect(globalExecutionTracker.getExecutionCount(messageId, handlerType)).toBe(0);

    globalExecutionTracker.track(messageId, handlerType);

    expect(globalExecutionTracker.getExecutionCount(messageId, handlerType)).toBe(1);
  });

  test("reset clears all tracked executions", () => {
    globalExecutionTracker.track("message-1", "HANDLER_A");
    globalExecutionTracker.track("message-2", "HANDLER_B");

    expect(globalExecutionTracker.getExecutionCount("message-1", "HANDLER_A")).toBe(1);

    globalExecutionTracker.reset();

    expect(globalExecutionTracker.getExecutionCount("message-1", "HANDLER_A")).toBe(0);
    expect(globalExecutionTracker.getExecutionCount("message-2", "HANDLER_B")).toBe(0);

    // Should be able to track again after reset
    expect(() => {
      globalExecutionTracker.track("message-1", "HANDLER_A");
    }).not.toThrow();
  });
});
