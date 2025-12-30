/**
 * Tests for custom error classes and ErrorHandler
 */

import { beforeEach, expect, test } from "bun:test";
import type { MockLogger } from "@fairfox/polly/test";
import { createMockLogger } from "@fairfox/polly/test";
import {
  APIError,
  ConnectionError,
  ErrorHandler,
  ExtensionError,
  HandlerError,
  MessageRouterError,
  OffscreenError,
  TimeoutError,
} from "@/shared/lib/errors";

let mockLogger: MockLogger;
let errorHandler: ErrorHandler;

beforeEach(() => {
  mockLogger = createMockLogger();
  errorHandler = new ErrorHandler(mockLogger);
});

// ============================================================================
// ExtensionError Base Class
// ============================================================================

test("ExtensionError - has correct properties", () => {
  const error = new ExtensionError("Test error", "TEST_CODE", {
    key: "value",
  });

  expect(error.message).toBe("Test error");
  expect(error.code).toBe("TEST_CODE");
  expect(error.context).toEqual({ key: "value" });
  expect(error.name).toBe("ExtensionError");
  expect(error instanceof Error).toBe(true);
  expect(error instanceof ExtensionError).toBe(true);
});

test("ExtensionError - works without context", () => {
  const error = new ExtensionError("Test error", "TEST_CODE");

  expect(error.message).toBe("Test error");
  expect(error.code).toBe("TEST_CODE");
  expect(error.context).toBeUndefined();
});

test("ExtensionError - has stack trace", () => {
  const error = new ExtensionError("Test error", "TEST_CODE");

  expect(error.stack).toBeDefined();
  expect(error.stack).toContain("ExtensionError");
});

// ============================================================================
// TimeoutError
// ============================================================================

test("TimeoutError - has timeout properties", () => {
  const error = new TimeoutError("Request timeout", 5000, {
    messageType: "SETTINGS_GET",
  });

  expect(error.message).toBe("Request timeout");
  expect(error.code).toBe("TIMEOUT_ERROR");
  expect(error.timeoutMs).toBe(5000);
  expect(error.context?.timeoutMs).toBe(5000);
  expect(error.context?.messageType).toBe("SETTINGS_GET");
  expect(error instanceof TimeoutError).toBe(true);
  expect(error instanceof ExtensionError).toBe(true);
});

// ============================================================================
// ConnectionError
// ============================================================================

test("ConnectionError - has correct code", () => {
  const error = new ConnectionError("Port disconnected", {
    portName: "content-123",
  });

  expect(error.message).toBe("Port disconnected");
  expect(error.code).toBe("CONNECTION_ERROR");
  expect(error.context?.portName).toBe("content-123");
  expect(error instanceof ConnectionError).toBe(true);
});

// ============================================================================
// MessageRouterError
// ============================================================================

test("MessageRouterError - has correct code", () => {
  const error = new MessageRouterError("No content script connected", {
    tabId: 123,
  });

  expect(error.message).toBe("No content script connected");
  expect(error.code).toBe("MESSAGE_ROUTER_ERROR");
  expect(error.context?.tabId).toBe(123);
  expect(error instanceof MessageRouterError).toBe(true);
});

// ============================================================================
// HandlerError
// ============================================================================

test("HandlerError - includes message type", () => {
  const error = new HandlerError("Handler failed", "SETTINGS_UPDATE", {
    reason: "validation",
  });

  expect(error.message).toBe("Handler failed");
  expect(error.code).toBe("HANDLER_ERROR");
  expect(error.messageType).toBe("SETTINGS_UPDATE");
  expect(error.context?.messageType).toBe("SETTINGS_UPDATE");
  expect(error.context?.reason).toBe("validation");
  expect(error instanceof HandlerError).toBe(true);
});

// ============================================================================
// APIError
// ============================================================================

test("APIError - includes status code", () => {
  const error = new APIError("API request failed", 404, {
    endpoint: "/api/users",
  });

  expect(error.message).toBe("API request failed");
  expect(error.code).toBe("API_ERROR");
  expect(error.statusCode).toBe(404);
  expect(error.context?.statusCode).toBe(404);
  expect(error.context?.endpoint).toBe("/api/users");
  expect(error instanceof APIError).toBe(true);
});

// ============================================================================
// OffscreenError
// ============================================================================

test("OffscreenError - has correct code", () => {
  const error = new OffscreenError("Failed to create offscreen document", {
    reason: "already exists",
  });

  expect(error.message).toBe("Failed to create offscreen document");
  expect(error.code).toBe("OFFSCREEN_ERROR");
  expect(error.context?.reason).toBe("already exists");
  expect(error instanceof OffscreenError).toBe(true);
});

// ============================================================================
// ErrorHandler.throw()
// ============================================================================

test("ErrorHandler.throw() - logs and throws error", () => {
  const error = new TimeoutError("Test timeout", 1000);

  expect(() => errorHandler.throw(error)).toThrow(error);

  // Should have logged the error
  const errorLog = mockLogger._calls.find((c) => c.level === "error");
  expect(errorLog).toBeDefined();
  expect(errorLog?.message).toBe("Test timeout");
  expect(errorLog?.error).toBe(error);
});

test("ErrorHandler.throw() - logs context", () => {
  const error = new MessageRouterError("Router error", {
    tabId: 456,
    messageType: "DOM_QUERY",
  });

  expect(() => errorHandler.throw(error)).toThrow(error);

  const errorLog = mockLogger._calls.find((c) => c.level === "error");
  expect(errorLog?.context?.tabId).toBe(456);
  expect(errorLog?.context?.messageType).toBe("DOM_QUERY");
});

// ============================================================================
// ErrorHandler.reject()
// ============================================================================

test("ErrorHandler.reject() - logs and returns error", () => {
  const error = new ConnectionError("Connection lost");

  const result = errorHandler.reject(error);

  expect(result).toBe(error);

  // Should have logged the error
  const errorLog = mockLogger._calls.find((c) => c.level === "error");
  expect(errorLog).toBeDefined();
  expect(errorLog?.message).toBe("Connection lost");
});

test("ErrorHandler.reject() - can be used in Promise.reject", async () => {
  const error = new TimeoutError("Test timeout", 100);

  const promise = Promise.reject(errorHandler.reject(error));

  await expect(promise).rejects.toBe(error);
  expect(mockLogger._calls).toHaveLength(1);
});

// ============================================================================
// ErrorHandler.wrap()
// ============================================================================

test("ErrorHandler.wrap() - wraps Error objects", () => {
  const originalError = new Error("Original error");

  const wrapped = errorHandler.wrap(originalError, "Operation failed", "OPERATION_ERROR", {
    operation: "test",
  });

  expect(wrapped.message).toBe("Operation failed: Original error");
  expect(wrapped.code).toBe("OPERATION_ERROR");
  expect(wrapped.context?.operation).toBe("test");
  expect(wrapped.context?.originalError).toBe("Original error");
  expect(wrapped.context?.originalStack).toBeDefined();
  expect(wrapped instanceof ExtensionError).toBe(true);
});

test("ErrorHandler.wrap() - wraps non-Error values", () => {
  const wrapped = errorHandler.wrap("string error", "Operation failed", "OPERATION_ERROR");

  expect(wrapped.message).toBe("Operation failed: string error");
  expect(wrapped.code).toBe("OPERATION_ERROR");
  expect(wrapped.context?.originalError).toBe("string error");
});

test("ErrorHandler.wrap() - preserves original stack trace", () => {
  const originalError = new Error("Original error");
  const originalStack = originalError.stack;

  const wrapped = errorHandler.wrap(originalError, "Operation failed", "OPERATION_ERROR");

  expect(wrapped.stack).toBe(originalStack);
});

test("ErrorHandler.wrap() - logs the wrapped error", () => {
  const originalError = new Error("Original");

  errorHandler.wrap(originalError, "Failed", "FAIL_CODE");

  const errorLog = mockLogger._calls.find((c) => c.level === "error");
  expect(errorLog).toBeDefined();
  expect(errorLog?.message).toBe("Failed: Original");
});

// ============================================================================
// Error Usage in Promise Chains
// ============================================================================

test("Errors work correctly in Promise chains", async () => {
  const operation = async () => {
    throw new TimeoutError("Async timeout", 500);
  };

  await expect(operation()).rejects.toThrow(TimeoutError);
  await expect(operation()).rejects.toMatchObject({
    code: "TIMEOUT_ERROR",
    timeoutMs: 500,
  });
});

test("Errors can be caught and inspected", async () => {
  try {
    throw new APIError("Not found", 404, { resource: "user" });
  } catch (error) {
    expect(error instanceof APIError).toBe(true);
    if (error instanceof APIError) {
      expect(error.statusCode).toBe(404);
      expect(error.context?.resource).toBe("user");
    }
  }
});

// ============================================================================
// Error Serialization
// ============================================================================

test("Errors can be serialized to JSON", () => {
  const error = new HandlerError("Handler failed", "TEST_MESSAGE", {
    attempt: 1,
  });

  const serialized = JSON.stringify({
    name: error.name,
    message: error.message,
    code: error.code,
    context: error.context,
  });

  const parsed = JSON.parse(serialized);
  expect(parsed.name).toBe("HandlerError");
  expect(parsed.message).toBe("Handler failed");
  expect(parsed.code).toBe("HANDLER_ERROR");
  expect(parsed.context.messageType).toBe("TEST_MESSAGE");
});
