import { beforeEach, expect, test } from "bun:test";
import {
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  createMockOffscreen,
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
} from "@fairfox/polly/test";
import { createBackground } from "@/background";
import { MessageRouter } from "@/background/message-router";
import type { ExtensionAdapters } from "@/shared/adapters";

beforeEach(() => {
  // Reset MessageRouter singleton before each test
  MessageRouter.resetInstance();
});

test("createBackground - works without adapters in Chrome environment", () => {
  // Skip this test if chrome is not defined (e.g., in Node.js without polyfill)
  if (typeof chrome === "undefined") {
    // This is expected in test environment - we'll test with mock adapters instead
    return;
  }

  const bus = createBackground();
  expect(bus).toBeDefined();
  expect(bus.context).toBe("background");
});

test("createBackground - works with mock adapters (no chrome global needed)", () => {
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

  const bus = createBackground(adapters);

  expect(bus).toBeDefined();
  expect(bus.context).toBe("background");
  expect(bus.adapters).toBe(adapters);
});

test("createBackground - message router is initialized", () => {
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

  const bus = createBackground(adapters);

  // Verify bus can register handlers (MessageRouter functionality)
  const handler = async () => ({
    data: { success: true },
    status: 200,
    statusText: "OK",
    headers: {},
  });
  bus.on("API_REQUEST", handler);

  expect(bus).toBeDefined();
});

test("createBackground - can be imported in Node.js with mock adapters", async () => {
  // This test simulates the issue from GitHub issue #25
  // where importing a file that calls createBackground() would fail
  // with "chrome is not defined" in Node.js verification environment

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
  const bus = createBackground(adapters);

  expect(bus).toBeDefined();
  expect(bus.context).toBe("background");
});
