import { beforeEach, expect, test } from "bun:test";
import type { MockExtensionAdapters } from "@fairfox/polly/test";
import { createMockAdapters } from "@fairfox/polly/test";
import { LogStore } from "@/background/log-store";
import { MessageBus } from "@/shared/lib/message-bus";

let backgroundAdapters: MockExtensionAdapters;
let backgroundBus: MessageBus;

beforeEach(() => {
  // Create adapter set for background context
  backgroundAdapters = createMockAdapters();

  // Create message bus
  backgroundBus = new MessageBus("background", backgroundAdapters);

  // Initialize LogStore in background (registers handlers)
  new LogStore(backgroundBus);
});

test("Integration - Background context logs to LogStore", async () => {
  // Send LOG message from background context
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Background test message",
    context: { userId: "123" },
    source: "background",
    timestamp: Date.now(),
  });

  // Verify log was stored
  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  expect(response.logs).toHaveLength(1);
  const log = response.logs[0];
  if (!log) throw new Error("Log entry not found");
  expect(log.message).toBe("Background test message");
  expect(log.source).toBe("background");
  expect(log.level).toBe("info");
  expect(log.context).toEqual({ userId: "123" });
});

test("Integration - Multiple contexts logging simultaneously", async () => {
  const now = Date.now();

  // Simulate logs from different contexts arriving at background
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "From background",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "warn",
    message: "From content",
    source: "content",
    timestamp: now + 1,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "From popup",
    error: "Test error",
    source: "popup",
    timestamp: now + 2,
  });

  // All logs should be in LogStore
  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  expect(response.logs).toHaveLength(3);

  const sources = response.logs.map((log) => log.source);
  expect(sources).toContain("background");
  expect(sources).toContain("content");
  expect(sources).toContain("popup");
});

test("Integration - LOG message creates proper log entries", async () => {
  const testError = new Error("Test error message");

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "An error occurred",
    context: { operation: "fetch", userId: "456" },
    error: testError.message,
    stack: testError.stack,
    source: "background",
    timestamp: Date.now(),
  });

  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  const log = response.logs[0];
  if (!log) throw new Error("Log entry not found");

  expect(log.level).toBe("error");
  expect(log.message).toBe("An error occurred");
  expect(log.error).toBe("Test error message");
  expect(log.stack).toBeDefined();
  expect(log.context).toEqual({ operation: "fetch", userId: "456" });
  expect(log.timestamp).toBeDefined();
  expect(log.id).toBeDefined();
});

test("Integration - All log levels are captured", async () => {
  const now = Date.now();

  await backgroundBus.send({
    type: "LOG",
    level: "debug",
    message: "Debug message",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Info message",
    source: "background",
    timestamp: now + 1,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "warn",
    message: "Warning message",
    source: "background",
    timestamp: now + 2,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "Error message",
    source: "background",
    timestamp: now + 3,
  });

  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  expect(response.logs).toHaveLength(4);

  const levels = response.logs.map((log) => log.level);
  expect(levels).toContain("debug");
  expect(levels).toContain("info");
  expect(levels).toContain("warn");
  expect(levels).toContain("error");
});

test("Integration - Query logs by source context", async () => {
  const now = Date.now();

  // Simulate logs from different contexts
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Background log 1",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Background log 2",
    source: "background",
    timestamp: now + 1,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Content log 1",
    source: "content",
    timestamp: now + 2,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Popup log 1",
    source: "popup",
    timestamp: now + 3,
  });

  // Query only content logs
  const response = await backgroundBus.send({
    type: "LOGS_GET",
    filters: { source: "content" },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(1);
  const log = response.logs[0];
  if (!log) throw new Error("Log entry not found");
  expect(log.message).toBe("Content log 1");
});

test("Integration - Query logs by level across contexts", async () => {
  const now = Date.now();

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Background info",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "Background error",
    source: "background",
    timestamp: now + 1,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Content info",
    source: "content",
    timestamp: now + 2,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "Content error",
    source: "content",
    timestamp: now + 3,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "warn",
    message: "Popup warning",
    source: "popup",
    timestamp: now + 4,
  });

  // Query only error logs
  const response = await backgroundBus.send({
    type: "LOGS_GET",
    filters: { level: "error" },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(2);
  const log0 = response.logs[0];
  const log1 = response.logs[1];
  if (!log0 || !log1) throw new Error("Log entries not found");
  expect(log0.message).toBe("Background error");
  expect(log1.message).toBe("Content error");
});

test("Integration - Clear logs", async () => {
  const now = Date.now();

  // Add logs
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Test log 1",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Test log 2",
    source: "content",
    timestamp: now + 1,
  });

  // Verify logs exist
  let response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  expect(response.logs).toHaveLength(2);

  // Clear logs
  const clearResponse = await backgroundBus.send({ type: "LOGS_CLEAR" });
  if (!clearResponse || !("success" in clearResponse)) throw new Error("Invalid response");
  expect(clearResponse.success).toBe(true);
  if (!("count" in clearResponse)) throw new Error("Missing count");
  expect(clearResponse.count).toBe(2);

  // Verify logs are cleared
  response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  expect(response.logs).toHaveLength(0);
});

test("Integration - Export logs", async () => {
  const now = Date.now();

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Export test",
    context: { data: "value" },
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "warn",
    message: "Warning to export",
    source: "content",
    timestamp: now + 1,
  });

  // Export logs
  const response = await backgroundBus.send({ type: "LOGS_EXPORT" });
  if (!response || !("json" in response)) throw new Error("Invalid response");

  expect(response.count).toBe(2);
  expect(response.json).toBeDefined();

  const logs = JSON.parse(response.json);
  expect(logs).toBeArray();
  expect(logs).toHaveLength(2);
  expect(logs[0].message).toBe("Export test");
  expect(logs[1].message).toBe("Warning to export");
});

test("Integration - High volume logging maintains circular buffer", async () => {
  // Create LogStore with small buffer
  const smallLogStore = new LogStore(backgroundBus, { maxLogs: 10 });

  const now = Date.now();

  // Generate 20 logs from various contexts
  for (let i = 0; i < 8; i++) {
    await backgroundBus.handleMessage({
      id: crypto.randomUUID(),
      source: "background",
      targets: ["background"],
      timestamp: now + i,
      payload: {
        type: "LOG",
        level: "info",
        message: `Background log ${i}`,
        source: "background",
        timestamp: now + i,
      },
    });
  }

  for (let i = 0; i < 7; i++) {
    await backgroundBus.handleMessage({
      id: crypto.randomUUID(),
      source: "content",
      targets: ["background"],
      timestamp: now + 8 + i,
      payload: {
        type: "LOG",
        level: "info",
        message: `Content log ${i}`,
        source: "content",
        timestamp: now + 8 + i,
      },
    });
  }

  for (let i = 0; i < 5; i++) {
    await backgroundBus.handleMessage({
      id: crypto.randomUUID(),
      source: "popup",
      targets: ["background"],
      timestamp: now + 15 + i,
      payload: {
        type: "LOG",
        level: "info",
        message: `Popup log ${i}`,
        source: "popup",
        timestamp: now + 15 + i,
      },
    });
  }

  // Should only have last 10 logs
  expect(smallLogStore.getCount()).toBe(10);

  const allLogs = smallLogStore.getAllLogs();
  expect(allLogs).toHaveLength(10);
});

test("Integration - MockLogger captures calls in test environment", () => {
  // In test environment, we use MockLogger

  // MockLogger should have captured calls functionality
  expect(backgroundAdapters.logger._calls).toBeDefined();
  expect(backgroundAdapters.logger._calls).toBeArray();

  // Make some log calls
  backgroundBus.adapters.logger.info("Test message", { key: "value" });
  backgroundBus.adapters.logger.error("Error message", new Error("Test"));

  // Verify calls were captured
  expect(backgroundAdapters.logger._calls).toHaveLength(2);
  const call0 = backgroundAdapters.logger._calls[0];
  const call1 = backgroundAdapters.logger._calls[1];
  if (!call0 || !call1) throw new Error("Logger calls not found");
  expect(call0.level).toBe("info");
  expect(call0.message).toBe("Test message");
  expect(call0.context).toEqual({ key: "value" });
  expect(call1.level).toBe("error");
  expect(call1.message).toBe("Error message");
});

test("Integration - MockLogger can be cleared between tests", () => {
  backgroundBus.adapters.logger.info("Test 1");
  backgroundBus.adapters.logger.info("Test 2");

  expect(backgroundAdapters.logger._calls).toHaveLength(2);

  // Clear captured calls
  backgroundAdapters.logger._clear();

  expect(backgroundAdapters.logger._calls).toHaveLength(0);
});

test("Integration - Timestamp ordering is preserved", async () => {
  const now = Date.now();

  // Send logs with controlled timestamps
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "First",
    source: "background",
    timestamp: now,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Second",
    source: "background",
    timestamp: now + 100,
  });

  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "Third",
    source: "background",
    timestamp: now + 200,
  });

  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  const log0 = response.logs[0];
  const log1 = response.logs[1];
  const log2 = response.logs[2];
  if (!log0 || !log1 || !log2) throw new Error("Log entries not found");
  expect(log0.message).toBe("First");
  expect(log1.message).toBe("Second");
  expect(log2.message).toBe("Third");
  expect(log0.timestamp).toBeLessThan(log1.timestamp);
  expect(log1.timestamp).toBeLessThan(log2.timestamp);
});

test("Integration - Context metadata is preserved in logs", async () => {
  // Log with rich context data
  await backgroundBus.send({
    type: "LOG",
    level: "info",
    message: "User action",
    context: {
      userId: "12345",
      action: "click",
      targets: ["button"],
      metadata: {
        page: "settings",
        timestamp: Date.now(),
        browser: "chrome",
      },
    },
    source: "background",
    timestamp: Date.now(),
  });

  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  const log = response.logs[0];
  if (!log) throw new Error("Log entry not found");

  expect(log.context?.userId).toBe("12345");
  expect(log.context?.action).toBe("click");
  if (!log.context?.metadata || typeof log.context.metadata !== "object") {
    throw new Error("Invalid metadata");
  }
  const metadata = log.context.metadata as Record<string, unknown>;
  expect(metadata.page).toBe("settings");
});

test("Integration - Error stack traces are captured", async () => {
  const error = new Error("Test error");

  await backgroundBus.send({
    type: "LOG",
    level: "error",
    message: "Operation failed",
    error: error.message,
    stack: error.stack,
    source: "background",
    timestamp: Date.now(),
  });

  const response = await backgroundBus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");
  const log = response.logs[0];
  if (!log) throw new Error("Log entry not found");

  expect(log.error).toBe("Test error");
  expect(log.stack).toBeDefined();
  expect(log.stack).toContain("Error");
});
