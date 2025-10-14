import { afterEach, beforeEach, expect, test } from "bun:test";
import { LogStore } from "@/background/log-store";
import { globalExecutionTracker } from "@/shared/lib/handler-execution-tracker";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage } from "@/shared/types/messages";
import { createMockAdapters } from "../helpers/adapters";

let bus: MessageBus;
let logStore: LogStore;

beforeEach(() => {
  const adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
  logStore = new LogStore(bus);
});

afterEach(() => {
  bus.destroy();
  globalExecutionTracker.reset();
});

test("LogStore - initializes with default options", () => {
  expect(logStore).toBeDefined();
  expect(logStore.getCount()).toBe(0);
  expect(logStore.getAllLogs()).toEqual([]);
});

test("LogStore - initializes with custom maxLogs", () => {
  const customStore = new LogStore(bus, { maxLogs: 500 });
  expect(customStore).toBeDefined();
  expect(customStore.getCount()).toBe(0);
});

test("LogStore - stores LOG messages", async () => {
  const message: ExtensionMessage = {
    type: "LOG",
    level: "info",
    message: "Test log message",
    source: "background",
    timestamp: Date.now(),
  };

  // Call handleMessage directly to test the LOG handler
  const response = await bus.handleMessage({
    id: "test-log-id",
    source: "background",
    targets: ["background"],
    timestamp: Date.now(),
    payload: message,
  });

  // Check what we got back
  expect(response).toBeDefined();
  if (typeof response === 'object' && response !== null && 'success' in response) {
    expect(response.success).toBe(true);
  }

  expect(logStore.getCount()).toBe(1);

  const logs = logStore.getAllLogs();
  const log0 = logs[0];
  if (!log0) throw new Error("Log entry not found");
  expect(log0.level).toBe("info");
  expect(log0.message).toBe("Test log message");
  expect(log0.source).toBe("background");
  expect(log0.id).toBeDefined();
});

test("LogStore - stores LOG with context and error", async () => {
  const message: ExtensionMessage = {
    type: "LOG",
    level: "error",
    message: "Error occurred",
    context: { userId: "123", action: "save" },
    error: "NetworkError",
    stack: "Error stack trace",
    source: "content",
    timestamp: Date.now(),
  };

  await bus.send(message);

  const logs = logStore.getAllLogs();
  const log0 = logs[0];
  if (!log0) throw new Error("Log entry not found");
  expect(log0.context).toEqual({ userId: "123", action: "save" });
  expect(log0.error).toBe("NetworkError");
  expect(log0.stack).toBe("Error stack trace");
});

test("LogStore - implements circular buffer (removes oldest)", async () => {
  const smallStore = new LogStore(bus, { maxLogs: 3 });

  // Add 5 logs
  for (let i = 0; i < 5; i++) {
    await bus.handleMessage({
      id: crypto.randomUUID(),
      source: "background",
      targets: ["background"],
      timestamp: Date.now(),
      payload: {
        type: "LOG",
        level: "info",
        message: `Log ${i}`,
        source: "background",
        timestamp: Date.now(),
      },
    });
  }

  expect(smallStore.getCount()).toBe(3);

  const logs = smallStore.getAllLogs();
  const log0 = logs[0];
  const log1 = logs[1];
  const log2 = logs[2];
  if (!log0 || !log1 || !log2) throw new Error("Log entries not found");
  expect(log0.message).toBe("Log 2"); // Oldest 2 removed
  expect(log1.message).toBe("Log 3");
  expect(log2.message).toBe("Log 4");
});

test("LogStore - LOGS_GET returns all logs without filters", async () => {
  // Add some logs
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 1",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "warn",
    message: "Log 2",
    source: "content",
    timestamp: Date.now(),
  });

  const response = await bus.send({ type: "LOGS_GET" });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toBeArray();
  expect(response.logs).toHaveLength(2);
});

test("LogStore - LOGS_GET filters by level", async () => {
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Info log",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "error",
    message: "Error log",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Another info",
    source: "background",
    timestamp: Date.now(),
  });

  const response = await bus.send({
    type: "LOGS_GET",
    filters: { level: "info" },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(2);
  const log0 = response.logs[0];
  const log1 = response.logs[1];
  if (!log0 || !log1) throw new Error("Log entries not found");
  expect(log0.message).toBe("Info log");
  expect(log1.message).toBe("Another info");
});

test("LogStore - LOGS_GET filters by source", async () => {
  await bus.send({
    type: "LOG",
    level: "info",
    message: "From background",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "From content",
    source: "content",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "From popup",
    source: "popup",
    timestamp: Date.now(),
  });

  const response = await bus.send({
    type: "LOGS_GET",
    filters: { source: "content" },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(1);
  const log0 = response.logs[0];
  if (!log0) throw new Error("Log entry not found");
  expect(log0.message).toBe("From content");
});

test("LogStore - LOGS_GET filters by timestamp", async () => {
  const now = Date.now();

  await bus.send({
    type: "LOG",
    level: "info",
    message: "Old log",
    source: "background",
    timestamp: now - 10000,
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Recent log",
    source: "background",
    timestamp: now,
  });

  const response = await bus.send({
    type: "LOGS_GET",
    filters: { since: now - 5000 },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(1);
  const log0 = response.logs[0];
  if (!log0) throw new Error("Log entry not found");
  expect(log0.message).toBe("Recent log");
});

test("LogStore - LOGS_GET limits results", async () => {
  // Add 5 logs
  for (let i = 0; i < 5; i++) {
    await bus.send({
      type: "LOG",
      level: "info",
      message: `Log ${i}`,
      source: "background",
      timestamp: Date.now(),
    });
  }

  const response = await bus.send({
    type: "LOGS_GET",
    filters: { limit: 2 },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(2);
  // Should return last 2 logs
  const log0 = response.logs[0];
  const log1 = response.logs[1];
  if (!log0 || !log1) throw new Error("Log entries not found");
  expect(log0.message).toBe("Log 3");
  expect(log1.message).toBe("Log 4");
});

test("LogStore - LOGS_GET combines multiple filters", async () => {
  const now = Date.now();

  await bus.send({
    type: "LOG",
    level: "info",
    message: "Background info",
    source: "background",
    timestamp: now,
  });
  await bus.send({
    type: "LOG",
    level: "error",
    message: "Content error",
    source: "content",
    timestamp: now,
  });
  await bus.send({
    type: "LOG",
    level: "error",
    message: "Background error",
    source: "background",
    timestamp: now,
  });

  const response = await bus.send({
    type: "LOGS_GET",
    filters: {
      level: "error",
      source: "background",
    },
  });
  if (!response || !("logs" in response)) throw new Error("Invalid response");

  expect(response.logs).toHaveLength(1);
  const log0 = response.logs[0];
  if (!log0) throw new Error("Log entry not found");
  expect(log0.message).toBe("Background error");
});

test("LogStore - LOGS_CLEAR removes all logs", async () => {
  // Add some logs
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 1",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 2",
    source: "background",
    timestamp: Date.now(),
  });

  expect(logStore.getCount()).toBe(2);

  const response = await bus.send({ type: "LOGS_CLEAR" });
  if (!response || !("success" in response)) throw new Error("Invalid response");

  expect(response.success).toBe(true);
  if (!("count" in response)) throw new Error("Missing count");
  expect(response.count).toBe(2); // Number of logs cleared
  expect(logStore.getCount()).toBe(0);
  expect(logStore.getAllLogs()).toEqual([]);
});

test("LogStore - LOGS_EXPORT returns JSON", async () => {
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Test log",
    source: "background",
    timestamp: 12345,
  });

  const response = await bus.send({ type: "LOGS_EXPORT" });
  if (!response || !("json" in response)) throw new Error("Invalid response");

  expect(response.json).toBeDefined();
  expect(response.count).toBe(1);

  const parsed = JSON.parse(response.json);
  expect(parsed).toBeArray();
  expect(parsed).toHaveLength(1);
  expect(parsed[0].message).toBe("Test log");
});

test("LogStore - handles empty export", async () => {
  const response = await bus.send({ type: "LOGS_EXPORT" });
  if (!response || !("json" in response)) throw new Error("Invalid response");

  expect(response.json).toBe("[]");
  expect(response.count).toBe(0);
});

test("LogStore - getCount returns current log count", async () => {
  expect(logStore.getCount()).toBe(0);

  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 1",
    source: "background",
    timestamp: Date.now(),
  });

  expect(logStore.getCount()).toBe(1);

  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 2",
    source: "background",
    timestamp: Date.now(),
  });

  expect(logStore.getCount()).toBe(2);
});

test("LogStore - getAllLogs returns copy of logs", async () => {
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Test log",
    source: "background",
    timestamp: Date.now(),
  });

  const logs1 = logStore.getAllLogs();
  const logs2 = logStore.getAllLogs();

  expect(logs1).toEqual(logs2);
  expect(logs1).not.toBe(logs2); // Different array instances
});

test("LogStore - generates unique IDs for each log", async () => {
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 1",
    source: "background",
    timestamp: Date.now(),
  });
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Log 2",
    source: "background",
    timestamp: Date.now(),
  });

  const logs = logStore.getAllLogs();
  const log0 = logs[0];
  const log1 = logs[1];
  if (!log0 || !log1) throw new Error("Log entries not found");
  expect(log0.id).toBeDefined();
  expect(log1.id).toBeDefined();
  expect(log0.id).not.toBe(log1.id);
});
