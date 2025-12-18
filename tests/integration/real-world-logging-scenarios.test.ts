/**
 * Real-world integration tests for logging and error handling
 *
 * These tests demonstrate complete scenarios that involve multiple
 * services, errors, and logging across the extension.
 */

import { afterEach, beforeEach, expect, test } from "bun:test";
import { LogStore } from "@/background/log-store";
import { MessageRouter } from "@/background/message-router";
import type { ExtensionAdapters } from "@/shared/adapters";
import { globalExecutionTracker } from "@/shared/lib/handler-execution-tracker";
import { MessageBus } from "@/shared/lib/message-bus";
import { settings } from "@/shared/state/app-state";
import type { LogEntry } from "@/shared/types/messages";
import {
  type MockLogger,
  type MockRuntime,
  createMockAdapters,
  createMockPort,
} from "../helpers/adapters";

let adapters: ExtensionAdapters;
let mockLogger: MockLogger;
let mockRuntime: MockRuntime;
let bus: MessageBus;

beforeEach(() => {
  // Reset MessageRouter singleton before each test
  MessageRouter.resetInstance();

  adapters = createMockAdapters();
  mockLogger = adapters.logger as MockLogger;
  mockRuntime = adapters.runtime as MockRuntime;
  bus = new MessageBus("background", adapters);
  new LogStore(bus);
});

afterEach(() => {
  bus.destroy();
  globalExecutionTracker.reset();
});

// ============================================================================
// Scenario: User Changes Settings
// ============================================================================

test("Scenario: User changes settings - full log trail", async () => {
  mockLogger._clear();

  // User updates settings directly via state
  settings.value = {
    ...settings.value,
    theme: "dark",
    notifications: true,
  };

  // Store logs in LogStore
  await bus.send({
    type: "LOG",
    level: "info",
    message: "User updated settings",
    context: { settings: { theme: "dark", notifications: true } },
    source: "background",
    timestamp: Date.now(),
  });

  // Can query the log later for debugging
  const logsResponse = await bus.send({
    type: "LOGS_GET",
    filters: { level: "info" },
  });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");

  const settingsLogs = logsResponse.logs.filter((log: unknown): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "message" in log &&
      typeof log.message === "string" &&
      (log.message.includes("settings") || log.message.includes("Settings"))
    );
  });

  expect(settingsLogs.length).toBeGreaterThan(0);
});

// ============================================================================
// Scenario: Error in Settings Update
// ============================================================================

test("Scenario: Settings update with state - persisted automatically", async () => {
  mockLogger._clear();

  // Update settings via state (automatically persisted)
  settings.value = {
    ...settings.value,
    theme: "light",
    notifications: false,
  };

  // State primitives handle persistence automatically
  expect(settings.value.theme).toBe("light");
  expect(settings.value.notifications).toBe(false);

  // Can still log manually if needed
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Settings updated via state",
    context: { settings: settings.value },
    source: "background",
    timestamp: Date.now(),
  });

  const logsResponse = await bus.send({
    type: "LOGS_GET",
    filters: { level: "info" },
  });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");

  expect(logsResponse.logs.length).toBeGreaterThan(0);
});

// ============================================================================
// Scenario: Multiple Tabs Connect
// ============================================================================

test("Scenario: Multiple content scripts connect", () => {
  new MessageRouter(bus);

  mockLogger._clear();

  // Three tabs open
  const tab1 = createMockPort("content-100");
  const tab2 = createMockPort("content-200");
  const tab3 = createMockPort("content-300");

  for (const listener of mockRuntime._connectListeners) {
    listener(tab1);
    listener(tab2);
    listener(tab3);
  }

  // Should log all three connections
  const connectionLogs = mockLogger._calls.filter((c) => c.message === "Port connected");

  expect(connectionLogs).toHaveLength(3);
  const log0 = connectionLogs[0];
  const log1 = connectionLogs[1];
  const log2 = connectionLogs[2];
  if (!log0 || !log1 || !log2) throw new Error("Connection logs not found");
  expect(log0.context?.port).toBe("content-100");
  expect(log1.context?.port).toBe("content-200");
  expect(log2.context?.port).toBe("content-300");

  // Can query logs to see connection history
  const debugLogs = mockLogger._calls.filter((c) => c.level === "debug");
  expect(debugLogs.length).toBeGreaterThan(0);
});

// ============================================================================
// Scenario: Tab Disconnects Unexpectedly
// ============================================================================

test("Scenario: Tab closes unexpectedly", () => {
  new MessageRouter(bus);

  // Tab connects
  const tab = createMockPort("content-123");
  for (const listener of mockRuntime._connectListeners) {
    listener(tab);
  }

  mockLogger._clear();

  // Tab suddenly disconnects (user closed tab)
  tab.disconnect();

  // Should log the disconnection
  const disconnectLog = mockLogger._calls.find((c) => c.message.includes("disconnected"));

  expect(disconnectLog).toBeDefined();
  expect(disconnectLog?.level).toBe("debug");
  expect(disconnectLog?.context?.tabId).toBe(123);
});

// ============================================================================
// Scenario: Message Sent to Closed Tab
// ============================================================================

test("Scenario: Attempt to message closed tab - warning logged", () => {
  const router = new MessageRouter(bus);

  mockLogger._clear();

  // Try to route message to non-existent tab
  router.routeMessage({
    id: "msg-123",
    source: "background",
    targets: ["content"],
    tabId: 999, // Doesn't exist
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  });

  // Should log warning
  const warnLog = mockLogger._calls.find((c) => c.level === "warn");

  expect(warnLog).toBeDefined();
  expect(warnLog?.message).toContain("port");
  expect(warnLog?.context?.tabId).toBe(999);
});

// ============================================================================
// Scenario: Debugging a Production Issue
// ============================================================================

test("Scenario: Debug production issue using logs", async () => {
  const sessionId = `session-${Date.now()}`;

  // Simulate a user action that goes through multiple services

  // 1. User initiates action
  await bus.send({
    type: "LOG",
    level: "info",
    message: "User action: Save preferences",
    context: { sessionId, action: "save-preferences" },
    source: "popup",
    timestamp: Date.now(),
  });

  // 2. Background processes it
  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Processing save request",
    context: { sessionId },
    source: "background",
    timestamp: Date.now(),
  });

  // 3. Storage operation
  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Writing to storage",
    context: { sessionId, keys: ["preferences"] },
    source: "background",
    timestamp: Date.now(),
  });

  // 4. Something fails
  await bus.send({
    type: "LOG",
    level: "error",
    message: "Failed to save preferences",
    context: { sessionId, error: "QUOTA_EXCEEDED" },
    error: "Storage quota exceeded",
    source: "background",
    timestamp: Date.now(),
  });

  // Now debug: Query all logs for this session
  const allLogsResponse = await bus.send({ type: "LOGS_GET" });
  if (!allLogsResponse || !("logs" in allLogsResponse)) throw new Error("Invalid response");
  const sessionLogs = allLogsResponse.logs.filter((log: unknown): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "context" in log &&
      typeof log.context === "object" &&
      log.context !== null &&
      "sessionId" in log.context &&
      log.context.sessionId === sessionId
    );
  });

  // Can see the entire flow
  expect(sessionLogs).toHaveLength(4);

  // Can see it started in popup
  const log0 = sessionLogs[0];
  const log1 = sessionLogs[1];
  if (!log0 || !log1) throw new Error("Session logs not found");
  expect(log0.source).toBe("popup");

  // Can see it was processed in background
  expect(log1.source).toBe("background");

  // Can see where it failed
  const errorLog = sessionLogs.find((log): log is LogEntry => {
    return typeof log === "object" && log !== null && "level" in log && log.level === "error";
  });
  expect(errorLog).toBeDefined();
  expect(errorLog?.context?.error).toBe("QUOTA_EXCEEDED");
});

// ============================================================================
// Scenario: Performance Issue Investigation
// ============================================================================

test("Scenario: Investigate slow operation with logs", async () => {
  const operationId = `op-${Date.now()}`;
  const startTime = Date.now();

  // Log operation steps with timestamps
  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Operation started",
    context: { operationId, step: "start" },
    source: "background",
    timestamp: startTime,
  });

  // Simulate slow step
  await new Promise((resolve) => setTimeout(resolve, 50));

  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Slow step completed",
    context: { operationId, step: "slow-step", duration: 50 },
    source: "background",
    timestamp: startTime + 50,
  });

  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Operation completed",
    context: { operationId, step: "end", totalDuration: 50 },
    source: "background",
    timestamp: startTime + 50,
  });

  // Query logs to analyze performance
  const logsResponse = await bus.send({ type: "LOGS_GET" });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");
  const opLogs = logsResponse.logs.filter((log: unknown): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "context" in log &&
      typeof log.context === "object" &&
      log.context !== null &&
      "operationId" in log.context &&
      log.context.operationId === operationId
    );
  });

  // Can see which step was slow
  expect(opLogs).toHaveLength(3);

  const slowStep = opLogs.find((log): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "context" in log &&
      typeof log.context === "object" &&
      log.context !== null &&
      "step" in log.context &&
      log.context.step === "slow-step"
    );
  });
  expect(slowStep).toBeDefined();
  expect(slowStep?.context?.duration).toBeGreaterThan(40);
});

// ============================================================================
// Scenario: Error Recovery Flow
// ============================================================================

test("Scenario: Operation fails and recovers with retry", async () => {
  const requestId = `req-${Date.now()}`;
  let attempt = 0;

  // First attempt fails
  attempt++;
  await bus.send({
    type: "LOG",
    level: "warn",
    message: "Operation failed, retrying",
    context: { requestId, attempt, error: "Network timeout" },
    source: "background",
    timestamp: Date.now(),
  });

  // Second attempt succeeds
  attempt++;
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Operation succeeded",
    context: { requestId, attempt },
    source: "background",
    timestamp: Date.now(),
  });

  // Query logs to see retry pattern
  const logsResponse = await bus.send({ type: "LOGS_GET" });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");
  const requestLogs = logsResponse.logs.filter((log: unknown): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "context" in log &&
      typeof log.context === "object" &&
      log.context !== null &&
      "requestId" in log.context &&
      log.context.requestId === requestId
    );
  });

  expect(requestLogs).toHaveLength(2);
  const reqLog0 = requestLogs[0];
  const reqLog1 = requestLogs[1];
  if (!reqLog0 || !reqLog1) throw new Error("Request logs not found");
  expect(reqLog0.level).toBe("warn");
  expect(reqLog1.level).toBe("info");
});

// ============================================================================
// Scenario: Export Logs for Bug Report
// ============================================================================

test("Scenario: User exports logs for bug report", async () => {
  // Simulate various operations that create logs
  await bus.send({
    type: "LOG",
    level: "info",
    message: "Extension loaded",
    source: "background",
    timestamp: Date.now(),
  });

  await bus.send({
    type: "LOG",
    level: "error",
    message: "Feature X failed",
    context: { feature: "X", userId: "user-123" },
    error: "Unexpected error",
    source: "content",
    timestamp: Date.now(),
  });

  await bus.send({
    type: "LOG",
    level: "warn",
    message: "Slow operation detected",
    context: { operation: "sync", duration: 5000 },
    source: "background",
    timestamp: Date.now(),
  });

  // User exports logs
  const exportResponse = await bus.send({ type: "LOGS_EXPORT" });
  if (!exportResponse || !("json" in exportResponse)) throw new Error("Invalid response");

  expect(exportResponse.json).toBeDefined();
  expect(exportResponse.count).toBe(3);

  // Parse the export
  const logs = JSON.parse(exportResponse.json);
  expect(logs).toBeArray();
  expect(logs).toHaveLength(3);

  // Verify structure
  if (!Array.isArray(logs)) {
    throw new Error("Logs is not an array");
  }
  for (const log of logs) {
    if (typeof log !== "object" || log === null) {
      throw new Error("Log entry is not an object");
    }
    expect(log.id).toBeDefined();
    expect(log.level).toBeDefined();
    expect(log.message).toBeDefined();
    expect(log.source).toBeDefined();
    expect(log.timestamp).toBeDefined();
  }
});

// ============================================================================
// Scenario: Filter Logs by Severity
// ============================================================================

test("Scenario: Developer reviews only errors and warnings", async () => {
  // Create logs of various levels
  await bus.send({
    type: "LOG",
    level: "debug",
    message: "Debug info",
    source: "background",
    timestamp: Date.now(),
  });

  await bus.send({
    type: "LOG",
    level: "info",
    message: "Normal operation",
    source: "background",
    timestamp: Date.now(),
  });

  await bus.send({
    type: "LOG",
    level: "warn",
    message: "Potential issue",
    source: "content",
    timestamp: Date.now(),
  });

  await bus.send({
    type: "LOG",
    level: "error",
    message: "Critical error",
    source: "background",
    timestamp: Date.now(),
  });

  // Query only errors and warnings
  const errorsResponse = await bus.send({
    type: "LOGS_GET",
    filters: { level: "error" },
  });
  if (!errorsResponse || !("logs" in errorsResponse)) throw new Error("Invalid response");

  const warningsResponse = await bus.send({
    type: "LOGS_GET",
    filters: { level: "warn" },
  });
  if (!warningsResponse || !("logs" in warningsResponse)) throw new Error("Invalid response");

  expect(errorsResponse.logs).toHaveLength(1);
  const errorLog = errorsResponse.logs[0];
  if (!errorLog) throw new Error("Error log not found");
  expect(errorLog.level).toBe("error");

  expect(warningsResponse.logs).toHaveLength(1);
  const warnLog = warningsResponse.logs[0];
  if (!warnLog) throw new Error("Warning log not found");
  expect(warnLog.level).toBe("warn");
});

// ============================================================================
// Scenario: Trace Cross-Context Message Flow
// ============================================================================

test("Scenario: Trace message flow across contexts", async () => {
  const messageId = `msg-${Date.now()}`;
  // Note: Not creating MessageRouter here to avoid duplicate LOGS_GET handlers

  // Connect content script (not used in this test, but simulates real scenario)
  const contentPort = createMockPort("content-123");
  for (const listener of mockRuntime._connectListeners) {
    listener(contentPort);
  }

  // Log message journey
  await bus.handleMessage({
    id: crypto.randomUUID(),
    source: "popup",
    targets: ["background"],
    timestamp: Date.now(),
    payload: {
      type: "LOG",
      level: "debug",
      message: "Message sent from popup",
      context: { messageId, destination: "content" },
      source: "popup",
      timestamp: Date.now(),
    },
  });

  await bus.handleMessage({
    id: crypto.randomUUID(),
    source: "background",
    targets: ["background"],
    timestamp: Date.now(),
    payload: {
      type: "LOG",
      level: "debug",
      message: "Message routed by background",
      context: { messageId, target: "content-123" },
      source: "background",
      timestamp: Date.now(),
    },
  });

  await bus.handleMessage({
    id: crypto.randomUUID(),
    source: "content",
    targets: ["background"],
    timestamp: Date.now(),
    payload: {
      type: "LOG",
      level: "debug",
      message: "Message received in content",
      context: { messageId },
      source: "content",
      timestamp: Date.now(),
    },
  });

  // Query logs to trace the message
  const logsResponse = await bus.send({ type: "LOGS_GET" });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");
  const messageLogs = logsResponse.logs.filter((log: unknown): log is LogEntry => {
    return (
      typeof log === "object" &&
      log !== null &&
      "context" in log &&
      typeof log.context === "object" &&
      log.context !== null &&
      "messageId" in log.context &&
      log.context.messageId === messageId
    );
  });

  // Can see the complete journey
  expect(messageLogs).toHaveLength(3);
  const msgLog0 = messageLogs[0];
  const msgLog1 = messageLogs[1];
  const msgLog2 = messageLogs[2];
  if (!msgLog0 || !msgLog1 || !msgLog2) throw new Error("Message logs not found");
  expect(msgLog0.source).toBe("popup");
  expect(msgLog1.source).toBe("background");
  expect(msgLog2.source).toBe("content");
});

// ============================================================================
// Scenario: Clear Logs After Debugging
// ============================================================================

test("Scenario: Clear logs after debugging session", async () => {
  // Create many logs during debugging
  for (let i = 0; i < 20; i++) {
    await bus.send({
      type: "LOG",
      level: "debug",
      message: `Debug log ${i}`,
      source: "background",
      timestamp: Date.now(),
    });
  }

  // Verify logs exist
  let logsResponse = await bus.send({ type: "LOGS_GET" });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");
  expect(logsResponse.logs).toHaveLength(20);

  // Clear logs
  const clearResponse = await bus.send({ type: "LOGS_CLEAR" });
  if (!clearResponse || !("success" in clearResponse)) throw new Error("Invalid response");
  expect(clearResponse.success).toBe(true);
  if (!("count" in clearResponse)) throw new Error("Missing count");
  expect(clearResponse.count).toBe(20);

  // Verify logs are cleared
  logsResponse = await bus.send({ type: "LOGS_GET" });
  if (!logsResponse || !("logs" in logsResponse)) throw new Error("Invalid response");
  expect(logsResponse.logs).toHaveLength(0);
});
