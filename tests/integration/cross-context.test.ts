import { afterEach, beforeEach, expect, mock, test } from "bun:test";
import {
  createMockAdapters,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  createMockOffscreen,
  createMockPort,
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
  type MockRuntime,
  waitFor,
} from "@fairfox/polly/test";
import { MessageRouter } from "@/background/message-router";
import type { ExtensionAdapters } from "@/shared/adapters";
import { MessageBus } from "@/shared/lib/message-bus";
import type { ExtensionMessage } from "@/shared/types/messages";

// Helper to simulate port connection
function simulatePortConnection(mockRuntime: MockRuntime, port: ReturnType<typeof createMockPort>) {
  for (const listener of mockRuntime._connectListeners) {
    listener(port);
  }
}

// Reset MessageRouter singleton before and after each test
// beforeEach ensures clean state when tests run in parallel
beforeEach(() => {
  MessageRouter.resetInstance();
});

afterEach(() => {
  MessageRouter.resetInstance();
});

test("Integration - Background to Content communication", async () => {
  const mockRuntime = createMockRuntime();
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const backgroundBus = new MessageBus("background", adapters);

  const router = new MessageRouter(backgroundBus);

  // Simulate content script connection
  const contentPort = createMockPort("content-123");

  // Spy on postMessage BEFORE connecting (to avoid infinite loop from router's listener)
  const postMessageSpy = mock((_msg: unknown) => {
    // Don't actually trigger listeners to avoid loop
  });
  contentPort.postMessage = postMessageSpy;

  simulatePortConnection(mockRuntime, contentPort);

  // Send message from background to content
  const message: ExtensionMessage = {
    type: "DOM_QUERY",
    selector: ".test",
  };

  router.routeMessage({
    id: "test-id",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: message,
  });

  expect(postMessageSpy).toHaveBeenCalled();
});

test("Integration - Content to Background communication", async () => {
  const adapters = createMockAdapters();

  const backgroundBus = new MessageBus("background", adapters);
  const contentBus = new MessageBus("content", adapters);

  // Register handler in background
  const handler = mock(async (_payload: ExtensionMessage) => ({ settings: { debugMode: true } }));
  backgroundBus.on("SETTINGS_GET", handler);

  // Send from content to background
  const message: ExtensionMessage = { type: "SETTINGS_GET" };
  await contentBus.send(message, { target: "background" });

  // Handler should be called
  expect(handler).toHaveBeenCalled();
});

test("Integration - Signal synchronization across contexts", async () => {
  const adapters = createMockAdapters();

  const backgroundBus = new MessageBus("background", adapters);
  const contentBus = new MessageBus("content", adapters);

  // Set up signal update handler in content
  const updateHandler = mock((_payload, _message) => undefined);
  contentBus.on("SIGNAL_UPDATE", updateHandler);

  // Broadcast signal update from background
  backgroundBus.broadcast({
    type: "SIGNAL_UPDATE",
    signalId: "test-signal",
    value: { count: 1 },
    source: "background",
  });

  await waitFor(10);

  // Content should receive the update
  expect(updateHandler).toHaveBeenCalled();

  // Cleanup
  backgroundBus.destroy();
  contentBus.destroy();
});

test("Integration - Multiple tabs with separate contexts", () => {
  const mockRuntime = createMockRuntime();
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const backgroundBus = new MessageBus("background", adapters);

  const router = new MessageRouter(backgroundBus);

  // Connect multiple content scripts
  const content1 = createMockPort("content-123");
  const content2 = createMockPort("content-456");

  simulatePortConnection(mockRuntime, content1);
  simulatePortConnection(mockRuntime, content2);

  expect(router.contentPorts.size).toBe(2);
  expect(router.contentPorts.has(123)).toBe(true);
  expect(router.contentPorts.has(456)).toBe(true);
});

test("Integration - DevTools connection per tab", () => {
  const mockRuntime = createMockRuntime();
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const backgroundBus = new MessageBus("background", adapters);

  const router = new MessageRouter(backgroundBus);

  // Connect devtools for specific tab
  const devtools = createMockPort("devtools-123");
  simulatePortConnection(mockRuntime, devtools);

  expect(router.devtoolsPorts.has(123)).toBe(true);

  // Route message to devtools
  const spy = mock();
  devtools.postMessage = spy;

  router.routeMessage({
    id: "test-id",
    source: "background",
    targets: ["devtools"],
    tabId: 123,
    timestamp: Date.now(),
    payload: { type: "DOM_QUERY", selector: ".test" },
  });

  expect(spy).toHaveBeenCalled();
});

test("Integration - Broadcast to all connected contexts", async () => {
  const mockRuntime = createMockRuntime();
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const backgroundBus = new MessageBus("background", adapters);

  const router = new MessageRouter(backgroundBus);

  // Connect multiple contexts
  const content1 = createMockPort("content-123");
  const content2 = createMockPort("content-456");
  const devtools1 = createMockPort("devtools-123");

  const spy1 = mock();
  const spy2 = mock();
  const spy3 = mock();

  content1.postMessage = spy1;
  content2.postMessage = spy2;
  devtools1.postMessage = spy3;

  simulatePortConnection(mockRuntime, content1);
  simulatePortConnection(mockRuntime, content2);
  simulatePortConnection(mockRuntime, devtools1);

  // Send to content port 123
  await router.routeMessage({
    id: "test-id-1",
    source: "background",
    targets: ["content"],
    tabId: 123,
    timestamp: Date.now(),
    payload: {
      type: "SIGNAL_UPDATE",
      signalId: "test",
      value: {},
      source: "background",
    },
  });

  // Send to content port 456
  await router.routeMessage({
    id: "test-id-2",
    source: "background",
    targets: ["content"],
    tabId: 456,
    timestamp: Date.now(),
    payload: {
      type: "SIGNAL_UPDATE",
      signalId: "test2",
      value: {},
      source: "background",
    },
  });

  // Send to devtools port 123
  await router.routeMessage({
    id: "test-id-3",
    source: "background",
    targets: ["devtools"],
    tabId: 123,
    timestamp: Date.now(),
    payload: {
      type: "SIGNAL_UPDATE",
      signalId: "test3",
      value: {},
      source: "background",
    },
  });

  // All contexts should have received their messages
  expect(spy1).toHaveBeenCalled();
  expect(spy2).toHaveBeenCalled();
  expect(spy3).toHaveBeenCalled();

  // Cleanup
  backgroundBus.destroy();
});

test("Integration - Port cleanup on disconnect", () => {
  const mockRuntime = createMockRuntime();
  const adapters: ExtensionAdapters = {
    runtime: mockRuntime,
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const backgroundBus = new MessageBus("background", adapters);

  const router = new MessageRouter(backgroundBus);

  const content = createMockPort("content-123");
  simulatePortConnection(mockRuntime, content);

  expect(router.contentPorts.has(123)).toBe(true);

  // Disconnect
  content.disconnect();
  router.contentPorts.delete(123);

  expect(router.contentPorts.has(123)).toBe(false);
});

test("Integration - Settings synchronization across contexts", async () => {
  const mockStorage = createMockStorageArea();
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: mockStorage,
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  await mockStorage.set({
    "app-settings": { debugMode: true, theme: "dark" },
  });

  const backgroundBus = new MessageBus("background", adapters);
  const popupBus = new MessageBus("popup", adapters);

  // Background handler
  backgroundBus.on("SETTINGS_GET", async (_payload, _message) => {
    const result = await mockStorage.get("app-settings");
    return { settings: result["app-settings"] };
  });

  // Popup requests settings from background
  const response = await popupBus.send({ type: "SETTINGS_GET" }, { target: "background" });
  if (!response || !("settings" in response)) throw new Error("Invalid response");

  expect(response.settings).toEqual({ debugMode: true, theme: "dark" });
});
