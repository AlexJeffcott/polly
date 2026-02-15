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

export type {
  MockChrome,
  MockContextMenus,
  MockExtensionAdapters,
  MockFetch,
  MockLogger,
  MockOffscreen,
  MockPort,
  MockRuntime,
  MockStorageArea,
  MockTabs,
  MockWindow,
} from "./adapters/index";
// Re-export all mock adapters
export {
  createMockAdapters,
  createMockChrome,
  createMockContextMenus,
  createMockFetch,
  createMockLogger,
  createMockOffscreen,
  createMockPort,
  createMockRuntime,
  createMockStorageArea,
  createMockTabs,
  createMockWindow,
} from "./adapters/index";

// Re-export test utilities
export {
  createMockRoutedMessage,
  expectType,
  noOp,
  noOpAsync,
  waitFor,
  waitForCondition,
} from "./test-utils";
