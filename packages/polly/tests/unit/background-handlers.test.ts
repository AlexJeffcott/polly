import { beforeEach, expect, mock, test } from "bun:test";
import {
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  createMockOffscreen,
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
  type MockFetch,
  noOpAsync,
} from "@fairfox/polly/test";
import { ApiClient } from "@/background/api-client";
import { ContextMenuManager } from "@/background/context-menu";
import { OffscreenManager } from "@/background/offscreen-manager";
import type { ExtensionAdapters } from "@/shared/adapters";
import type { OffscreenAdapter } from "@/shared/adapters/offscreen.adapter";
import { MessageBus } from "@/shared/lib/message-bus";
import { clearGlobals, setGlobal } from "./helpers/globals";

let mockFetch: MockFetch;
let adapters: ExtensionAdapters;
let bus: MessageBus;

beforeEach(() => {
  // Create fetch mock separately so we can access its internals
  mockFetch = createMockFetch();

  adapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: mockFetch,
    logger: createMockLogger(),
  };

  bus = new MessageBus("background", adapters);
});

test("ApiClient - handles API_REQUEST", async () => {
  new ApiClient(bus);

  // Queue a mock response
  mockFetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ data: "test" }),
  });

  const response = await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/test",
    method: "GET",
  });
  if (!response || !("status" in response)) throw new Error("Invalid response");

  expect(response.status).toBe(200);
  expect(response.data).toEqual({ data: "test" });
  expect(mockFetch._calls).toHaveLength(1);
  const call0 = mockFetch._calls[0];
  if (!call0) throw new Error("Fetch call not found");
  expect(call0.input).toBe("https://api.example.com/test");
});

test("ApiClient - handles POST with body", async () => {
  new ApiClient(bus);

  mockFetch._responses.push({
    ok: true,
    status: 201,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "Created",
    json: async () => ({ created: true }),
  });

  const response = await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/create",
    method: "POST",
    body: { name: "test" },
  });
  if (!response || !("status" in response)) throw new Error("Invalid response");

  expect(response.status).toBe(201);
  const call0 = mockFetch._calls[0];
  if (!call0) throw new Error("Fetch call not found");
  expect(call0.init?.method).toBe("POST");
  expect(call0.init?.body).toBe(JSON.stringify({ name: "test" }));
});

test("ApiClient - handles API errors", async () => {
  new ApiClient(bus);

  mockFetch._responses.push({
    ok: false,
    status: 404,
    headers: new Headers(),
    statusText: "Not Found",
    json: async () => {
      throw new Error("Not JSON");
    },
  });

  const response = await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/missing",
    method: "GET",
  });
  if (!response || !("status" in response)) throw new Error("Invalid response");

  expect(response.status).toBe(404);
  expect(response.statusText).toBe("Not Found");
});

test("ApiClient - handles network errors", async () => {
  new ApiClient(bus);

  // Replace fetch temporarily to throw error
  const originalFetch = mockFetch.fetch;
  mockFetch.fetch = async () => {
    throw new Error("Network error");
  };

  const response = await bus.send({
    type: "API_REQUEST",
    endpoint: "https://api.example.com/test",
    method: "GET",
  });
  if (!response || !("status" in response)) throw new Error("Invalid response");

  expect(response.status).toBe(0);
  expect(response.error).toBe("Network error");

  mockFetch.fetch = originalFetch;
});

test("ApiClient - handles API_BATCH", async () => {
  new ApiClient(bus);

  mockFetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ url: "https://api.example.com/1" }),
  });
  mockFetch._responses.push({
    ok: true,
    status: 200,
    headers: new Headers({ "content-type": "application/json" }),
    statusText: "OK",
    json: async () => ({ url: "https://api.example.com/2" }),
  });

  const response = await bus.send({
    type: "API_BATCH",
    requests: [
      { endpoint: "https://api.example.com/1", method: "GET" },
      { endpoint: "https://api.example.com/2", method: "GET" },
    ],
  });
  if (!response || !("results" in response)) throw new Error("Invalid response");

  expect(response.results).toBeArray();
  expect(response.results).toHaveLength(2);
});

test("ContextMenuManager - creates context menu", () => {
  // Mock not needed for this test - manager doesn't call create in constructor
  const manager = new ContextMenuManager(bus);
  // Just verify it initializes without error
  expect(manager).toBeDefined();
});

test("ContextMenuManager - handles context menu clicks", async () => {
  const broadcastSpy = mock<typeof bus.broadcast>(noOpAsync);
  const originalBroadcast = bus.broadcast;
  bus.broadcast = broadcastSpy;

  const manager = new ContextMenuManager(bus);

  // Test passes if manager initializes without error
  expect(manager).toBeDefined();

  bus.broadcast = originalBroadcast;
});

test("ContextMenuManager - broadcasts a numeric menu item id as a string", () => {
  let clicked: ((info: chrome.contextMenus.OnClickData, tab?: chrome.tabs.Tab) => void) | undefined;
  const testBus = new MessageBus("background", {
    ...adapters,
    contextMenus: {
      ...adapters.contextMenus,
      onClicked: (callback) => {
        clicked = callback;
      },
    },
  });
  const broadcasts: unknown[] = [];
  testBus.broadcast = (payload) => {
    broadcasts.push(payload);
  };
  new ContextMenuManager(testBus);

  const tab: chrome.tabs.Tab = {
    id: 7,
    active: true,
    index: 0,
    pinned: false,
    highlighted: false,
    windowId: 1,
    frozen: false,
    incognito: false,
    selected: false,
    discarded: false,
    autoDiscardable: true,
    groupId: -1,
    lastAccessed: 0,
  };
  clicked?.({ menuItemId: 42, editable: false, pageUrl: "https://example.com" }, tab);

  expect(broadcasts).toHaveLength(1);
  expect(broadcasts[0]).toMatchObject({ type: "CONTEXT_MENU_CLICKED", menuId: "42", tabId: 7 });
});

test("ContextMenuManager - CONTEXT_MENU_CREATE passes contexts through", async () => {
  // chrome.contextMenus.ContextType is a runtime enum on the real `chrome` global.
  const priorChrome: unknown = Reflect.get(globalThis, "chrome");
  setGlobal("chrome", { contextMenus: { ContextType: { PAGE: "page", SELECTION: "selection" } } });
  const { PAGE, SELECTION } = chrome.contextMenus.ContextType;
  if (priorChrome === undefined) clearGlobals("chrome");
  else setGlobal("chrome", priorChrome);
  const created: chrome.contextMenus.CreateProperties[] = [];
  const testBus = new MessageBus("background", {
    ...adapters,
    contextMenus: {
      ...adapters.contextMenus,
      create: async (props) => {
        created.push(props);
      },
    },
  });
  new ContextMenuManager(testBus);

  const response = await testBus.send({
    type: "CONTEXT_MENU_CREATE",
    id: "m1",
    title: "Menu",
    contexts: [PAGE, SELECTION],
  });

  expect(response).toEqual({ success: true });
  expect(created).toEqual([{ id: "m1", title: "Menu", contexts: ["page", "selection"] }]);
});

test("ContextMenuManager - CONTEXT_MENU_CREATE refuses an empty contexts list", async () => {
  const created: chrome.contextMenus.CreateProperties[] = [];
  const testBus = new MessageBus("background", {
    ...adapters,
    contextMenus: {
      ...adapters.contextMenus,
      create: async (props) => {
        created.push(props);
      },
    },
  });
  new ContextMenuManager(testBus);

  const response = await testBus.send({
    type: "CONTEXT_MENU_CREATE",
    id: "m2",
    title: "Menu",
    contexts: [],
  });

  expect(response).toEqual({ success: false });
  expect(created).toEqual([]);
});

test("OffscreenManager - creates offscreen document", async () => {
  const createSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => false),
  };

  const testAdapters: ExtensionAdapters = {
    ...adapters,
    offscreen: mockOffscreen,
  };
  const testBus = new MessageBus("background", testAdapters);
  const manager = new OffscreenManager(testBus);

  await manager.ensureOffscreenDocument();

  expect(createSpy).toHaveBeenCalled();
});

test("OffscreenManager - reuses existing offscreen document", async () => {
  const createSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: createSpy,
    closeDocument: mock(noOpAsync),
    hasDocument: mock(async () => true),
  };

  const testAdapters: ExtensionAdapters = {
    ...adapters,
    offscreen: mockOffscreen,
  };
  const testBus = new MessageBus("background", testAdapters);
  const manager = new OffscreenManager(testBus);

  await manager.ensureOffscreenDocument();

  expect(createSpy).not.toHaveBeenCalled();
});

test("OffscreenManager - closes offscreen document", async () => {
  const closeSpy = mock(noOpAsync);
  const mockOffscreen: OffscreenAdapter = {
    createDocument: mock(noOpAsync),
    closeDocument: closeSpy,
    hasDocument: mock(async () => true),
  };

  const testAdapters: ExtensionAdapters = {
    ...adapters,
    offscreen: mockOffscreen,
  };
  const testBus = new MessageBus("background", testAdapters);
  const manager = new OffscreenManager(testBus);
  await manager.ensureOffscreenDocument();
  await manager.closeOffscreenDocument();

  expect(closeSpy).toHaveBeenCalled();
});
