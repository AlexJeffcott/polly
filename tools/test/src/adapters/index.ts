import { type MockContextMenus, createMockContextMenus } from "./context-menus.mock";
import { type MockFetch, createMockFetch } from "./fetch.mock";
import { type MockLogger, createMockLogger } from "./logger.mock";
import { type MockOffscreen, createMockOffscreen } from "./offscreen.mock";
import { type MockPort, type MockRuntime, createMockPort, createMockRuntime } from "./runtime.mock";
import { type MockStorageArea, createMockStorageArea } from "./storage.mock";
import { type MockTabs, createMockTabs } from "./tabs.mock";
import { type MockWindow, createMockWindow } from "./window.mock";

/**
 * Mock adapters with full type information including mock-specific properties
 */
export interface MockExtensionAdapters {
  runtime: MockRuntime;
  storage: MockStorageArea;
  tabs: MockTabs;
  window: MockWindow;
  offscreen: MockOffscreen;
  contextMenus: MockContextMenus;
  fetch: MockFetch;
  logger: MockLogger;
}

/**
 * Convenience interface grouping Chrome-like mock APIs
 * Useful when tests need direct access to internal mock state
 */
export interface MockChrome {
  runtime: MockRuntime;
  storage: {
    local: MockStorageArea;
  };
  tabs: MockTabs;
}

/**
 * Create a mock Chrome object with grouped APIs
 * Use this when you need access to internal mock state (e.g., mockChrome.tabs._tabs)
 */
export function createMockChrome(): MockChrome {
  return {
    runtime: createMockRuntime(),
    storage: {
      local: createMockStorageArea(),
    },
    tabs: createMockTabs(),
  };
}

/**
 * Create a complete set of mock adapters for testing
 * Returns mock adapters with full type information
 */
export function createMockAdapters(): MockExtensionAdapters {
  return {
    runtime: createMockRuntime(),
    storage: createMockStorageArea(),
    tabs: createMockTabs(),
    window: createMockWindow(),
    offscreen: createMockOffscreen(),
    contextMenus: createMockContextMenus(),
    fetch: createMockFetch(),
    logger: createMockLogger({ silent: true }),
  };
}

// Re-export individual mock factories and types for convenience
export {
  createMockRuntime,
  createMockPort,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
  createMockOffscreen,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
};

export type {
  MockRuntime,
  MockPort,
  MockStorageArea,
  MockTabs,
  MockWindow,
  MockOffscreen,
  MockContextMenus,
  MockFetch,
  MockLogger,
};
