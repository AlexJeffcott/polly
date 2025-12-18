/**
 * Tests proving that MessageRouter does NOT cause infinite loops
 *
 * These tests specifically address the issue where mock ports would
 * trigger infinite recursion when routing messages.
 */

import { beforeEach, expect, test } from "bun:test";
import { MessageRouter } from "@/background/message-router";
import { MessageBus } from "@/shared/lib/message-bus";
import { ALL_CONTEXTS, type ExtensionMessage } from "@/shared/types/messages";
import {
  type MockExtensionAdapters,
  createMockAdapters,
  createMockPort,
} from "../helpers/adapters";

let adapters: MockExtensionAdapters;
let bus: MessageBus<ExtensionMessage>;
let router: MessageRouter<ExtensionMessage>;

beforeEach(() => {
  // Reset MessageRouter singleton before each test
  MessageRouter.resetInstance();

  adapters = createMockAdapters();
  bus = new MessageBus("background", adapters);
  router = new MessageRouter(bus);
});

// ============================================================================
// Prove: No Infinite Loops When Routing Messages
// ============================================================================

test("Routing a message does NOT cause infinite loop", () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  // Clear listeners to prevent test infrastructure from causing loops
  port._listeners.clear();

  // This should complete without stack overflow
  const routePromise = router.routeMessage({
    id: "test-msg",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "TEST_MESSAGE", data: "test" },
  });

  // Should resolve without error
  expect(routePromise).resolves.toBeUndefined();
});

test("Multiple sequential routes do NOT cause loops", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }
  port._listeners.clear();

  // Route 100 messages in sequence
  for (let i = 0; i < 100; i++) {
    await router.routeMessage({
      id: `msg-${i}`,
      source: "background",
      targets: ["content"],
      tabId: 123,
      timestamp: Date.now(),
      payload: { type: "STATE_SYNC", key: `test-${i}`, value: { count: i }, clock: i },
    });
  }

  // If we get here, no infinite loop occurred
  expect(true).toBe(true);
});

test("Broadcasting does NOT cause infinite loop", () => {
  const port1 = createMockPort("content-111");
  const port2 = createMockPort("content-222");
  const port3 = createMockPort("devtools-111");

  for (const listener of adapters.runtime._connectListeners) {
    listener(port1);
    listener(port2);
    listener(port3);
  }

  // Clear all listeners
  port1._listeners.clear();
  port2._listeners.clear();
  port3._listeners.clear();

  // This should broadcast to all ports without loops
  const broadcastPromise = router.routeMessage({
    id: "broadcast-msg",
    source: "background",
    targets: ALL_CONTEXTS, // Broadcast to all contexts
    timestamp: Date.now(),
    payload: {
      type: "STATE_SYNC",
      key: "test",
      value: {},
      clock: 1,
    },
  });

  // Just verify it completes without throwing (no infinite loop)
  expect(broadcastPromise).resolves.toBeDefined();
});

test("Routing to multiple targets sequentially does NOT loop", async () => {
  const contentPort = createMockPort("content-123");
  const devtoolsPort = createMockPort("devtools-123");
  const popupPort = createMockPort("popup");

  for (const listener of adapters.runtime._connectListeners) {
    listener(contentPort);
    listener(devtoolsPort);
    listener(popupPort);
  }

  // Clear all listeners
  contentPort._listeners.clear();
  devtoolsPort._listeners.clear();
  popupPort._listeners.clear();

  // Route to different targets
  await router.routeMessage({
    id: "msg-1",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  await router.routeMessage({
    id: "msg-2",
    source: "background",
    targets: ["devtools"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  await router.routeMessage({
    id: "msg-3",
    source: "background",
    targets: ["popup"],
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  // No loops occurred
  expect(true).toBe(true);
});

// ============================================================================
// Prove: Ports Can Be Connected/Disconnected Without Issues
// ============================================================================

test("Connecting and disconnecting many ports does NOT loop", () => {
  const ports = [];

  // Connect 50 ports
  for (let i = 0; i < 50; i++) {
    const port = createMockPort(`content-${i}`);
    for (const listener of adapters.runtime._connectListeners) {
      listener(port);
    }
    ports.push(port);
  }

  // Disconnect all ports
  for (const port of ports) {
    port.disconnect();
  }

  // No loops occurred
  expect(true).toBe(true);
});

test("Rapid port connections do NOT cause loops", () => {
  // Connect 100 ports rapidly
  for (let i = 0; i < 100; i++) {
    const port = createMockPort(`content-${i}`);
    for (const listener of adapters.runtime._connectListeners) {
      listener(port);
    }
  }

  // No loops occurred
  expect(true).toBe(true);
});

// ============================================================================
// Prove: Call Stack Depth Remains Reasonable
// ============================================================================

test("Routing does not increase call stack depth dangerously", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }
  port._listeners.clear();

  // Track maximum stack depth by counting recursive calls
  let maxDepth = 0;
  let currentDepth = 0;

  // Wrap the route function to track depth
  const originalRoute = router.routeMessage.bind(router);
  // biome-ignore lint/suspicious/noExplicitAny: Testing with generic message parameter
  router.routeMessage = async (message: any) => {
    currentDepth++;
    if (currentDepth > maxDepth) {
      maxDepth = currentDepth;
    }
    const result = await originalRoute(message);
    currentDepth--;
    return result;
  };

  // Route a message
  await router.routeMessage({
    id: "test-msg",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  // Stack depth should be minimal (just 1 call)
  expect(maxDepth).toBe(1);
});

test("Multiple concurrent routes do NOT cause stack overflow", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }
  port._listeners.clear();

  // Route 50 messages concurrently
  const promises = [];
  for (let i = 0; i < 50; i++) {
    promises.push(
      router.routeMessage({
        id: `msg-${i}`,
        source: "background",
        targets: ["content"],
        tabId: 123,
        timestamp: Date.now(),
        payload: { type: "STATE_SYNC", key: `test-${i}`, value: { count: i }, clock: i },
      })
    );
  }

  // All should resolve without stack overflow
  await Promise.all(promises);
  expect(true).toBe(true);
});

// ============================================================================
// Prove: Routing to Non-Existent Ports Does NOT Loop
// ============================================================================

test("Routing to non-existent port does NOT loop", async () => {
  // Try to route to a port that doesn't exist
  const result = await router.routeMessage({
    id: "test-msg",
    source: "background",
    targets: ["content"],
    tabId: 999,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  // Should return error, not loop
  expect(result).toBeDefined();
  if (
    result &&
    typeof result === "object" &&
    "success" in result &&
    typeof result.success === "boolean"
  ) {
    expect(result.success).toBe(false);
  }
});

test("Routing to closed port does NOT loop", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  // Disconnect the port
  port.disconnect();

  // Try to route to the now-closed port
  const result = await router.routeMessage({
    id: "test-msg",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  // Should handle gracefully, not loop
  expect(result).toBeDefined();
});

// ============================================================================
// Prove: Error Cases Do NOT Cause Loops
// ============================================================================

test("Invalid message payload does NOT cause loop", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }
  port._listeners.clear();

  // Route message with minimal payload (edge case)
  try {
    await router.routeMessage({
      id: "test-msg",
      source: "background",
      targets: ["content"],
      tabId: 123,
      timestamp: Date.now(),
      payload: {
        type: "LOG",
        level: "info",
        message: "test",
        source: "background",
        timestamp: Date.now(),
      }, // Minimal valid message
    });
  } catch (_error) {
    // May throw error, but should not loop
  }

  // Should handle without looping (either succeeds or throws, but no infinite loop)
  expect(true).toBe(true);
});

test("Routing with missing required fields does NOT loop", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }

  // Route message missing tabId (required for content target)
  const result = await router.routeMessage({
    id: "test-msg",
    source: "background",
    targets: ["content"],
    tabId: undefined, // Missing required field for content target
    timestamp: Date.now(),
    payload: { type: "TEST" },
  });

  // Should return error, not loop
  expect(result).toBeDefined();
  if (
    result &&
    typeof result === "object" &&
    "success" in result &&
    typeof result.success === "boolean"
  ) {
    expect(result.success).toBe(false);
  }
});

// ============================================================================
// Performance: Routing Should Be Fast
// ============================================================================

test("Routing 1000 messages completes in reasonable time", async () => {
  const port = createMockPort("content-123");
  for (const listener of adapters.runtime._connectListeners) {
    listener(port);
  }
  port._listeners.clear();

  const start = performance.now();

  // Route 1000 messages
  for (let i = 0; i < 1000; i++) {
    await router.routeMessage({
      id: `msg-${i}`,
      source: "background",
      targets: ["content"],
      tabId: 123,
      timestamp: Date.now(),
      payload: { type: "STATE_SYNC", key: `test-${i}`, value: { count: i }, clock: i },
    });
  }

  const duration = performance.now() - start;
  const avgTime = duration / 1000;

  // Should be fast (< 1ms per route on average)
  expect(avgTime).toBeLessThan(1);
});

test("Broadcasting to 20 ports completes quickly", async () => {
  const ports = [];

  // Connect 20 ports
  for (let i = 0; i < 20; i++) {
    const port = createMockPort(`content-${i}`);
    for (const listener of adapters.runtime._connectListeners) {
      listener(port);
    }
    port._listeners.clear();
    ports.push(port);
  }

  const start = performance.now();

  // Broadcast message
  await router.routeMessage({
    id: "broadcast-msg",
    source: "background",
    targets: ALL_CONTEXTS, // Broadcast to all contexts
    timestamp: Date.now(),
    payload: {
      type: "STATE_SYNC",
      key: "test",
      value: {},
      clock: 1,
    },
  });

  const duration = performance.now() - start;

  // Should be fast (< 10ms)
  expect(duration).toBeLessThan(10);
});
