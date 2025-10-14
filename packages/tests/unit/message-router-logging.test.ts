/**
 * Tests for MessageRouter logging behavior
 */

import { beforeEach, expect, test } from "bun:test";
import { MessageRouter } from "@/background/message-router";
import { MessageBus } from "@/shared/lib/message-bus";
import {
  type MockExtensionAdapters,
  createMockAdapters,
  createMockPort,
} from "../helpers/adapters";

let adapters: MockExtensionAdapters;
let bus: MessageBus;
let router: MessageRouter;

beforeEach(() => {
  adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
  router = new MessageRouter(bus);
});

// ============================================================================
// Port Connection Logging
// ============================================================================

test("MessageRouter logs content port connections", () => {
  adapters.logger._clear();

  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  // Should log port connection
  const connectionLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "Port connected"
  );

  expect(connectionLog).toBeDefined();
  expect(connectionLog?.level).toBe("debug");
  expect(connectionLog?.context?.port).toBe("content-123");
});

test("MessageRouter logs devtools port connections", () => {
  adapters.logger._clear();

  const port = createMockPort("devtools-456");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  const connectionLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "Port connected"
  );

  expect(connectionLog).toBeDefined();
  expect(connectionLog?.context?.port).toBe("devtools-456");
});

test("MessageRouter logs popup port connections", () => {
  adapters.logger._clear();

  const port = createMockPort("popup");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  const connectionLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "Port connected"
  );

  expect(connectionLog).toBeDefined();
  expect(connectionLog?.context?.port).toBe("popup");
});

test("MessageRouter logs offscreen port connections", () => {
  adapters.logger._clear();

  const port = createMockPort("offscreen");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  const connectionLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "Port connected"
  );

  expect(connectionLog).toBeDefined();
  expect(connectionLog?.context?.port).toBe("offscreen");
});

// ============================================================================
// Port Disconnection Logging
// ============================================================================

test("MessageRouter logs content port disconnections", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  // Disconnect port
  port.disconnect();

  const disconnectLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "Content port disconnected"
  );

  expect(disconnectLog).toBeDefined();
  expect(disconnectLog?.level).toBe("debug");
  expect(disconnectLog?.context?.tabId).toBe(123);
});

test("MessageRouter logs devtools port disconnections", () => {
  const port = createMockPort("devtools-456");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  port.disconnect();

  const disconnectLog = adapters.logger._calls.find(
    (c: { message: string }) => c.message === "DevTools port disconnected"
  );

  expect(disconnectLog).toBeDefined();
  expect(disconnectLog?.context?.tabId).toBe(456);
});

// ============================================================================
// Message Routing Logging
// ============================================================================

test("MessageRouter logs when routing messages", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  // Clear port listeners to prevent infinite loop in test
  port._listeners.clear();

  router.routeMessage({
    id: "test-msg-id",
    source: "background",
    target: "content",
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  });

  // Should log routing activity
  const routingLogs = adapters.logger._calls.filter(
    (c: { level?: string; message: string }) => c.level === "debug" && c.message.includes("Routing")
  );

  expect(routingLogs.length).toBeGreaterThan(0);
});

test("MessageRouter logs warning when port not found", () => {
  adapters.logger._clear();

  // Try to route to non-existent port
  router.routeMessage({
    id: "test-msg-id",
    source: "background",
    target: "content",
    tabId: 999, // Non-existent
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  });

  // Should log warning
  const warningLog = adapters.logger._calls.find(
    (c: { level?: string; message: string }) => c.level === "warn" && c.message.includes("port")
  );

  expect(warningLog).toBeDefined();
  expect(warningLog?.context?.tabId).toBe(999);
});

test("MessageRouter includes message type in routing logs", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  // Clear port listeners to prevent infinite loop in test
  port._listeners.clear();

  router.routeMessage({
    id: "test-msg-id",
    source: "background",
    target: "content",
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "CUSTOM_MESSAGE", data: "test" },
  });

  const routingLog = adapters.logger._calls.find((c: { context?: unknown }) => {
    if (c.context && typeof c.context === "object" && "type" in c.context) {
      return c.context.type === "CUSTOM_MESSAGE";
    }
    return false;
  });

  expect(routingLog).toBeDefined();
});

// ============================================================================
// Multiple Port Connections
// ============================================================================

test("MessageRouter logs multiple port connections distinctly", () => {
  adapters.logger._clear();

  const port1 = createMockPort("content-111");
  const port2 = createMockPort("content-222");
  const port3 = createMockPort("devtools-111");

  for (const listener of adapters.runtime._connectListeners) {
    listener(port1);
    listener(port2);
    listener(port3);
  }

  const connectionLogs = adapters.logger._calls.filter(
    (c: { message: string }) => c.message === "Port connected"
  );

  expect(connectionLogs).toHaveLength(3);
  expect(connectionLogs[0]?.context?.port).toBe("content-111");
  expect(connectionLogs[1]?.context?.port).toBe("content-222");
  expect(connectionLogs[2]?.context?.port).toBe("devtools-111");
});

// ============================================================================
// Broadcast Logging
// ============================================================================

test("MessageRouter logs broadcast messages", () => {
  const port1 = createMockPort("content-111");
  const port2 = createMockPort("content-222");

  for (const listener of adapters.runtime._connectListeners) {
    listener(port1);
    listener(port2);
  }

  adapters.logger._clear();

  // Clear port listeners to prevent infinite loop in test
  port1._listeners.clear();
  port2._listeners.clear();

  router.routeMessage({
    id: "broadcast-msg",
    source: "background",
    target: "broadcast",
    timestamp: Date.now(),
    payload: {
      type: "SIGNAL_UPDATE",
      signalId: "test",
      value: {},
      source: "background",
    },
  });

  // Should have debug logs for broadcast routing
  const debugLogs = adapters.logger._calls.filter((c: { level?: string }) => c.level === "debug");
  expect(debugLogs.length).toBeGreaterThan(0);
});

// ============================================================================
// Invalid Port Names
// ============================================================================

test("MessageRouter logs all port connections including invalid names", () => {
  adapters.logger._clear();

  const invalidPort = createMockPort("invalid-port-format");
  for (const listener of adapters.runtime._connectListeners) {
    listener(invalidPort);
  }

  // Should log connection even for invalid port names (for debugging)
  const connectionLogs = adapters.logger._calls.filter(
    (c: { message: string; context?: unknown }) => {
      if (
        c.message === "Port connected" &&
        c.context &&
        typeof c.context === "object" &&
        "port" in c.context
      ) {
        return c.context.port === "invalid-port-format";
      }
      return false;
    }
  );

  // Router logs all connections, even if it doesn't handle them
  expect(connectionLogs).toHaveLength(1);
});

// ============================================================================
// Log Structure Validation
// ============================================================================

test("MessageRouter logs have consistent structure", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  const allLogs = adapters.logger._calls;

  // All logs should have required fields
  for (const log of allLogs) {
    expect(log.level).toBeDefined();
    expect(log.message).toBeDefined();
    expect(log.timestamp).toBeDefined();
    expect(typeof log.level).toBe("string");
    expect(typeof log.message).toBe("string");
    expect(typeof log.timestamp).toBe("number");
  }
});

// ============================================================================
// No Sensitive Data in Logs
// ============================================================================

test("MessageRouter does not log message payloads (potential sensitive data)", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  // Clear port listeners to prevent infinite loop in test
  port._listeners.clear();

  router.routeMessage({
    id: "sensitive-msg",
    source: "background",
    target: "content",
    tabId: 123,
    timestamp: Date.now(),
    payload: {
      type: "USER_DATA",
      password: "super-secret-password",
      apiKey: "sk-1234567890",
    },
  });

  const allLogs = JSON.stringify(adapters.logger._calls);

  // Sensitive data should NOT appear in logs
  expect(allLogs).not.toContain("super-secret-password");
  expect(allLogs).not.toContain("sk-1234567890");

  // But message type is OK to log
  expect(allLogs).toContain("USER_DATA");
});

// ============================================================================
// Port Replacement Logging
// ============================================================================

test("MessageRouter logs when replacing existing port", () => {
  const port1 = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port1);
  }

  adapters.logger._clear();

  // Connect second port with same tab ID (replaces first)
  const port2 = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port2);
  }

  const connectionLogs = adapters.logger._calls.filter(
    (c: { message: string; context?: unknown }) => {
      if (
        c.message === "Port connected" &&
        c.context &&
        typeof c.context === "object" &&
        "port" in c.context
      ) {
        return c.context.port === "content-123";
      }
      return false;
    }
  );

  // Should log the new connection
  expect(connectionLogs).toHaveLength(1);
});

// ============================================================================
// Performance: Logging Should Be Fast
// ============================================================================

test("MessageRouter logging does not significantly impact performance", () => {
  const iterations = 100;

  const start = performance.now();

  for (let i = 0; i < iterations; i++) {
    const port = createMockPort(`content-${i}`);
    for (const listener of adapters.runtime._connectListeners) {
      listener(port);
    }
  }

  const duration = performance.now() - start;
  const avgTimePerConnection = duration / iterations;

  // Should be very fast (< 1ms per connection)
  expect(avgTimePerConnection).toBeLessThan(1);
});

// ============================================================================
// Log Levels Are Appropriate
// ============================================================================

test("MessageRouter uses appropriate log levels", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  adapters.logger._clear();

  // Try to route to non-existent port (no infinite loop risk since port doesn't exist)
  router.routeMessage({
    id: "test-msg",
    source: "background",
    target: "content",
    tabId: 999,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  const debugLogs = adapters.logger._calls.filter((c: { level?: string }) => c.level === "debug");
  const warnLogs = adapters.logger._calls.filter((c: { level?: string }) => c.level === "warn");
  const errorLogs = adapters.logger._calls.filter((c: { level?: string }) => c.level === "error");

  // Routing should log with debug
  expect(debugLogs.length).toBeGreaterThan(0);

  // Missing port should be warn
  expect(warnLogs.length).toBeGreaterThan(0);

  // Normal operations should not produce errors
  expect(errorLogs.length).toBe(0);
});
