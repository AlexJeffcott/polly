import { beforeEach, expect, mock, test } from "bun:test";
import { MessageRouter } from "@/background/message-router";
import type { ExtensionAdapters } from "@/shared/adapters";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage, RoutedMessage } from "@/shared/types/messages";
import {
  type MockRuntime,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  createMockOffscreen,
  createMockPort,
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
} from "@fairfox/polly/test";

let mockRuntime: MockRuntime;
let adapters: ExtensionAdapters;
let bus: MessageBus<ExtensionMessage>;
let router: MessageRouter<ExtensionMessage>;

beforeEach(() => {
  // Reset MessageRouter singleton before each test
  MessageRouter.resetInstance();

  // Create runtime mock separately so we can access its internals
  mockRuntime = createMockRuntime();

  adapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  bus = new MessageBus("background", adapters);
  router = new MessageRouter(bus);
});

test("MessageRouter - initializes with empty port maps", () => {
  expect(router.contentPorts).toBeInstanceOf(Map);
  expect(router.devtoolsPorts).toBeInstanceOf(Map);
  expect(router.contentPorts.size).toBe(0);
  expect(router.devtoolsPorts.size).toBe(0);
});

test("MessageRouter - registers content script port", () => {
  const port = createMockPort("content-123");

  // Simulate port connection by calling the registered onConnect callback
  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  expect(router.contentPorts.has(123)).toBe(true);
  expect(router.contentPorts.get(123)).toBe(port);
});

test("MessageRouter - registers devtools port", () => {
  const port = createMockPort("devtools-456");

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  expect(router.devtoolsPorts.has(456)).toBe(true);
  expect(router.devtoolsPorts.get(456)).toBe(port);
});

test("MessageRouter - ignores invalid port names", () => {
  const port = createMockPort("invalid-port-name");

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  expect(router.contentPorts.size).toBe(0);
  expect(router.devtoolsPorts.size).toBe(0);
});

test("MessageRouter - cleans up on content port disconnect", () => {
  const port = createMockPort("content-123");

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }
  expect(router.contentPorts.has(123)).toBe(true);

  port.disconnect();

  expect(router.contentPorts.has(123)).toBe(false);
});

test("MessageRouter - cleans up on devtools port disconnect", () => {
  const port = createMockPort("devtools-456");

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }
  expect(router.devtoolsPorts.has(456)).toBe(true);

  port.disconnect();

  expect(router.devtoolsPorts.has(456)).toBe(false);
});

test("MessageRouter - routes message to content script", () => {
  const port = createMockPort("content-123");
  const postMessageSpy = mock();
  port.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  };

  router.routeMessage(message);

  expect(postMessageSpy).toHaveBeenCalledWith(message);
});

test("MessageRouter - routes message to devtools", () => {
  const port = createMockPort("devtools-456");
  const postMessageSpy = mock();
  port.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["devtools"],
    tabId: 456,
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  };

  router.routeMessage(message);

  expect(postMessageSpy).toHaveBeenCalledWith(message);
});

test("MessageRouter - broadcasts to all content scripts", async () => {
  const port1 = createMockPort("content-123");
  const port2 = createMockPort("content-456");
  const spy1 = mock();
  const spy2 = mock();
  port1.postMessage = spy1;
  port2.postMessage = spy2;

  for (const listener of mockRuntime._connectListeners) {
    listener(port1);
    listener(port2);
  }

  // Send to content context (which will broadcast to all content ports)
  const message1: RoutedMessage = {
    id: "test-id-1",
    source: "background",
    targets: ["content"], // Target content context
    tabId: 123,
    timestamp: Date.now(),
    payload: {
      type: "STATE_SYNC",
      key: "test",
      value: {},
      clock: 1,
    },
  };

  await router.routeMessage(message1);
  expect(spy1).toHaveBeenCalled();

  // Send to another content script
  const message2: RoutedMessage = {
    id: "test-id-2",
    source: "background",
    targets: ["content"],
    tabId: 456,
    timestamp: Date.now(),
    payload: {
      type: "STATE_SYNC",
      key: "test2",
      value: {},
      clock: 2,
    },
  };

  await router.routeMessage(message2);
  expect(spy2).toHaveBeenCalled();
});

test("MessageRouter - handles missing port gracefully", () => {
  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["content"],
    tabId: 999, // non-existent tab
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  };

  // Should not throw
  expect(() => router.routeMessage(message)).not.toThrow();
});

test("MessageRouter - tracks multiple tabs", () => {
  const port1 = createMockPort("content-123");
  const port2 = createMockPort("content-456");
  const port3 = createMockPort("devtools-123");

  for (const listener of mockRuntime._connectListeners) {
    listener(port1);
    listener(port2);
    listener(port3);
  }

  expect(router.contentPorts.size).toBe(2);
  expect(router.devtoolsPorts.size).toBe(1);
});

test("MessageRouter - routes to popup", async () => {
  const popupPort = createMockPort("popup");
  const postMessageSpy = mock();
  popupPort.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(popupPort);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["popup"],
    timestamp: Date.now(),
    payload: { type: "TAB_QUERY", queryInfo: {} },
  };

  await router.routeMessage(message);

  expect(postMessageSpy).toHaveBeenCalledWith(message);
});

test("MessageRouter - routes to options", async () => {
  const optionsPort = createMockPort("options");
  const postMessageSpy = mock();
  optionsPort.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(optionsPort);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["options"],
    timestamp: Date.now(),
    payload: { type: "TAB_QUERY", queryInfo: {} },
  };

  await router.routeMessage(message);

  expect(postMessageSpy).toHaveBeenCalledWith(message);
});

test("MessageRouter - routes to offscreen", async () => {
  const offscreenPort = createMockPort("offscreen");
  const postMessageSpy = mock();
  offscreenPort.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(offscreenPort);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["offscreen"],
    timestamp: Date.now(),
    payload: { type: "CLIPBOARD_WRITE", text: "test" },
  };

  await router.routeMessage(message);

  expect(postMessageSpy).toHaveBeenCalledWith(message);
});

test("MessageRouter - extracts tabId from port name", () => {
  const port = createMockPort("content-789");
  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }

  expect(router.contentPorts.has(789)).toBe(true);
});

test("MessageRouter - handles malformed port names", () => {
  const ports = [
    createMockPort("content-"), // Missing tabId -> NaN
    createMockPort("content-abc"), // Invalid tabId -> NaN
    createMockPort("contentXYZ"), // No dash separator -> undefined
    createMockPort("devtools-"), // Missing tabId -> NaN
  ];

  for (const port of ports) {
    for (const listener of mockRuntime._connectListeners) {
      listener(port);
    }
  }

  // Malformed ports are now handled safely:
  // 'content-' (missing tabId) -> defaults to 0
  // 'content-abc' (invalid tabId) -> NaN, filtered out by isNaN check
  // 'contentXYZ' (no dash) -> no context match, not added
  // 'devtools-' (missing tabId) -> defaults to 0

  // NaN values are filtered out, so they're never added
  expect(router.contentPorts.has(Number.NaN)).toBe(false);
  expect(router.devtoolsPorts.has(Number.NaN)).toBe(false);

  // Missing tabId defaults to 0, so those ARE added
  expect(router.contentPorts.has(0)).toBe(true);
  expect(router.devtoolsPorts.has(0)).toBe(true);
});

test("MessageRouter - routes page script messages through content script", () => {
  const contentPort = createMockPort("content-123");
  const postMessageSpy = mock();
  contentPort.postMessage = postMessageSpy;

  for (const listener of mockRuntime._connectListeners) {
    listener(contentPort);
  }

  const message: RoutedMessage = {
    id: "test-id",
    source: "background",
    targets: ["page"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "PAGE_EVAL", code: 'console.log("test")' },
  };

  router.routeMessage(message);

  // Page messages go through content script
  expect(postMessageSpy).toHaveBeenCalled();
});

test("MessageRouter - handles concurrent port connections", () => {
  const ports = [
    createMockPort("content-1"),
    createMockPort("content-2"),
    createMockPort("content-3"),
    createMockPort("devtools-1"),
    createMockPort("devtools-2"),
  ];

  for (const port of ports) {
    for (const listener of mockRuntime._connectListeners) {
      listener(port);
    }
  }

  expect(router.contentPorts.size).toBe(3);
  expect(router.devtoolsPorts.size).toBe(2);
});

test("MessageRouter - replaces port for same tab", () => {
  const port1 = createMockPort("content-123");
  const port2 = createMockPort("content-123");

  for (const listener of mockRuntime._connectListeners) {
    listener(port1);
  }
  expect(router.contentPorts.get(123)).toBe(port1);

  for (const listener of mockRuntime._connectListeners) {
    listener(port2);
  }
  expect(router.contentPorts.get(123)).toBe(port2);
  expect(router.contentPorts.size).toBe(1);
});
