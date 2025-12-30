import { createMockContextMenus, type MockContextMenus } from "./context-menus.mock";
import { createMockFetch, type MockFetch } from "./fetch.mock";
import { createMockLogger, type MockLogger } from "./logger.mock";
import { createMockOffscreen, type MockOffscreen } from "./offscreen.mock";
import { createMockPort, createMockRuntime, type MockPort, type MockRuntime } from "./runtime.mock";
import { createMockStorageArea, type MockStorageArea } from "./storage.mock";
import { createMockTabs, type MockTabs } from "./tabs.mock";
import { createMockWindow, type MockWindow } from "./window.mock";

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
