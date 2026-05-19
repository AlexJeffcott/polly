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
  noOpAsync,
} from "@fairfox/polly/test";
import { MessageRouter } from "@/background/message-router";
import type { ExtensionAdapters } from "@/shared/adapters";
import { createContext } from "@/shared/lib/context-helpers";

beforeEach(() => {
  // Reset MessageRouter singleton before each test
  MessageRouter.resetInstance();
});

test("createContext - works with mock adapters (no chrome global needed)", () => {
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const bus = createContext("popup", {
    adapters,
    waitForDOM: false, // Skip DOM wait in tests
  });

  expect(bus).toBeDefined();
  expect(bus.context).toBe("popup");
  expect(bus.adapters).toBe(adapters);
});

test("createContext - calls onInit callback", async () => {
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const onInitMock = mock(noOpAsync);

  const bus = createContext("options", {
    adapters,
    waitForDOM: false,
    onInit: onInitMock,
  });

  // Wait a tick for async initialization
  await new Promise((resolve) => setTimeout(resolve, 10));

  expect(onInitMock).toHaveBeenCalledWith(bus);
});

test("createContext - calls onError when onInit fails", async () => {
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const error = new Error("Init failed");
  const onInitMock = mock(async () => {
    throw error;
  });
  const onErrorMock = mock(() => {
    // No-op: just tracking if this gets called
  });

  const bus = createContext("sidepanel", {
    adapters,
    waitForDOM: false,
    onInit: onInitMock,
    onError: onErrorMock,
  });

  // Wait for async initialization to complete
  await new Promise((resolve) => setTimeout(resolve, 10));

  expect(onInitMock).toHaveBeenCalled();
  expect(onErrorMock).toHaveBeenCalledWith(error, bus);
});

test("createContext - can register handlers", () => {
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const bus = createContext("content", {
    adapters,
    waitForDOM: false,
  });

  // Verify bus can register handlers
  const handler = async () => ({
    data: { success: true },
    status: 200,
    statusText: "OK",
    headers: {},
  });
  bus.on("API_REQUEST", handler);

  expect(bus).toBeDefined();
});

test("createContext - works for different contexts", () => {
  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  const contexts = ["popup", "options", "content", "devtools", "sidepanel"] as const;

  for (const context of contexts) {
    const bus = createContext(context, {
      adapters,
      waitForDOM: false,
    });

    expect(bus).toBeDefined();
    expect(bus.context).toBe(context);
  }
});

test("createContext - solves GitHub issue #25 chrome is not defined problem", () => {
  // This test verifies that createContext() can be used in Node.js
  // verification environments without needing the chrome global

  const adapters: ExtensionAdapters = {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger(),
  };

  // This should not throw "chrome is not defined"
  const bus = createContext("popup", {
    adapters,
    waitForDOM: false,
  });

  expect(bus).toBeDefined();
  expect(bus.context).toBe("popup");
});
