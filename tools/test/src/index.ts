/**
 * Public API for @fairfox/polly/test
 *
 * Provides test utilities and mock adapters for testing Polly applications.
 *
 * @example
 * ```typescript
 * import { createMockAdapters, waitForCondition } from '@fairfox/polly/test'
 *
 * test('message handling', async () => {
 *   const adapters = createMockAdapters()
 *   const bus = new MessageBus('background', adapters)
 *
 *   await waitForCondition(() => bus.isConnected)
 * })
 * ```
 */

// Re-export all mock adapters
export {
  createMockAdapters,
  createMockChrome,
  createMockRuntime,
  createMockPort,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
  createMockOffscreen,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
} from "./adapters/index";

export type {
  MockExtensionAdapters,
  MockChrome,
  MockRuntime,
  MockPort,
  MockStorageArea,
  MockTabs,
  MockWindow,
  MockOffscreen,
  MockContextMenus,
  MockFetch,
  MockLogger,
} from "./adapters/index";

// Re-export test utilities
export {
  createMockRoutedMessage,
  waitFor,
  waitForCondition,
  expectType,
  noOp,
  noOpAsync,
} from "./test-utils";
