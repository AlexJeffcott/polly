import { expect, mock, test } from "bun:test";
import type { TabsAdapter } from "@/shared/adapters";
import type { MessageSender } from "@/shared/adapters/runtime.adapter";
import { createMockChrome, createMockPort, createMockStorageArea } from "@fairfox/polly/test";

/**
 * Adapter interface tests - these test the mock implementations
 * Real Chrome adapter implementations are tested in E2E tests with actual Chrome APIs
 */

test("RuntimeAdapter interface - sendMessage", async () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  // Set up mock response
  mockChrome.runtime.onMessage((message: unknown, _sender, sendResponse) => {
    if (
      typeof message === "object" &&
      message !== null &&
      "type" in message &&
      message.type === "TEST"
    ) {
      sendResponse({ success: true });
    }
    return undefined;
  });

  const response = await adapter.sendMessage({ type: "TEST" });
  expect(response).toEqual({ success: true });
});

test("RuntimeAdapter interface - onMessage listener", async () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  const callback = mock((_message: unknown, _sender, _sendResponse) => {
    if (typeof _message === "object" && _message !== null && "type" in _message) {
      expect(_message.type).toBe("TEST");
    }
    return undefined;
  });

  adapter.onMessage(callback);

  // Simulate incoming message
  for (const listener of mockChrome.runtime._messageListeners) {
    // biome-ignore lint/suspicious/noEmptyBlockStatements: Empty response handler for test
    listener({ type: "TEST" }, {} as MessageSender, () => {});
  }

  expect(callback).toHaveBeenCalled();
});

test("RuntimeAdapter interface - connect creates port", () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  const port = adapter.connect("test-port");
  expect(port.name).toBe("test-port");
});

test("RuntimeAdapter interface - onConnect listener", () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  const callback = mock((port) => {
    expect(port.name).toBe("test-connection");
  });

  adapter.onConnect(callback);

  // Simulate connection
  adapter.connect("test-connection");

  expect(callback).toHaveBeenCalled();
});

test("RuntimeAdapter interface - getURL", () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  const url = adapter.getURL("popup/popup.html");
  expect(url).toContain("chrome-extension://");
  expect(url).toContain("popup/popup.html");
});

test("RuntimeAdapter interface - getId", () => {
  const mockChrome = createMockChrome();
  const adapter = mockChrome.runtime;

  const id = adapter.getId();
  expect(id).toBe("test-extension-id");
});

test("StorageAdapter interface - get single key", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ testKey: "testValue" });

  const adapter = mockStorage;
  const result = await adapter.get("testKey");

  expect(result).toEqual({ testKey: "testValue" });
});

test("StorageAdapter interface - get multiple keys", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ key1: "value1", key2: "value2" });

  const adapter = mockStorage;
  const result = await adapter.get(["key1", "key2"]);

  expect(result).toEqual({ key1: "value1", key2: "value2" });
});

test("StorageAdapter interface - get with defaults", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ existingKey: "existingValue" });

  const adapter = mockStorage;
  const result = await adapter.get({
    existingKey: "default1",
    missingKey: "default2",
  });

  expect(result).toEqual({
    existingKey: "existingValue",
    missingKey: "default2",
  });
});

test("StorageAdapter interface - set items", async () => {
  const mockStorage = createMockStorageArea();
  const adapter = mockStorage;

  await adapter.set({ key1: "value1", key2: "value2" });

  expect(mockStorage._data.get("key1")).toBe("value1");
  expect(mockStorage._data.get("key2")).toBe("value2");
});

test("StorageAdapter interface - remove single key", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ key1: "value1", key2: "value2" });

  const adapter = mockStorage;
  await adapter.remove("key1");

  expect(mockStorage._data.has("key1")).toBe(false);
  expect(mockStorage._data.has("key2")).toBe(true);
});

test("StorageAdapter interface - remove multiple keys", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ key1: "value1", key2: "value2", key3: "value3" });

  const adapter = mockStorage;
  await adapter.remove(["key1", "key2"]);

  expect(mockStorage._data.has("key1")).toBe(false);
  expect(mockStorage._data.has("key2")).toBe(false);
  expect(mockStorage._data.has("key3")).toBe(true);
});

test("StorageAdapter interface - clear all", async () => {
  const mockStorage = createMockStorageArea();
  await mockStorage.set({ key1: "value1", key2: "value2" });

  const adapter = mockStorage;
  await adapter.clear();

  expect(mockStorage._data.size).toBe(0);
});

test("TabsAdapter interface - query tabs", async () => {
  const mockChrome = createMockChrome();
  const tab1: chrome.tabs.Tab = {
    id: 1,
    index: 0,
    pinned: false,
    highlighted: false,
    windowId: 1,
    active: true,
    incognito: false,
    selected: true,
    discarded: false,
    autoDiscardable: true,
    groupId: -1,
    url: "https://example.com",
    title: "Test",
  };
  const tab2: chrome.tabs.Tab = {
    id: 2,
    index: 1,
    pinned: false,
    highlighted: false,
    windowId: 1,
    active: false,
    incognito: false,
    selected: false,
    discarded: false,
    autoDiscardable: true,
    groupId: -1,
    url: "https://test.com",
    title: "Test 2",
  };
  mockChrome.tabs._tabs.set(1, tab1);
  mockChrome.tabs._tabs.set(2, tab2);

  const adapter = mockChrome.tabs;
  const tabs = await adapter.query({});

  expect(tabs).toBeArray();
  expect(tabs).toHaveLength(2);
});

test("TabsAdapter interface - query active tab", async () => {
  const mockChrome = createMockChrome();
  mockChrome.tabs._tabs.set(1, {
    id: 1,
    url: "https://example.com",
    title: "Test",
    active: true,
    index: 0,
    pinned: false,
    highlighted: false,
    windowId: 1,
    incognito: false,
    selected: true,
    discarded: false,
    autoDiscardable: true,
    groupId: -1,
  });

  const adapter: TabsAdapter = mockChrome.tabs;
  const tabs = await adapter.query({ active: true });

  expect(tabs).toBeArray();
  expect(tabs).toHaveLength(1);
});

test("TabsAdapter interface - sendMessage to tab", async () => {
  const mockChrome = createMockChrome();
  const adapter: TabsAdapter = mockChrome.tabs;

  const response = await adapter.sendMessage(1, { type: "TEST" });
  expect(response).toEqual({ success: true });
});

test("Port - message passing", () => {
  const port = createMockPort("test-port");
  const callback = mock((message: unknown) => {
    expect((message as { type: string }).type).toBe("TEST");
  });

  port.onMessage(callback);
  port.postMessage({ type: "TEST" });

  expect(callback).toHaveBeenCalled();
});

test("Port - disconnect", () => {
  const port = createMockPort("test-port");
  const callback = mock();

  port.onDisconnect(callback);
  port.disconnect();

  expect(callback).toHaveBeenCalled();
});

test("Port - multiple listeners", () => {
  const port = createMockPort("test-port");
  const callback1 = mock();
  const callback2 = mock();

  port.onMessage(callback1);
  port.onMessage(callback2);
  port.postMessage({ type: "TEST" });

  expect(callback1).toHaveBeenCalled();
  expect(callback2).toHaveBeenCalled();
});
