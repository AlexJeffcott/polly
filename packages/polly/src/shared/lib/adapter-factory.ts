// Adapter factory for automatically creating storage and sync adapters

import { createStorageAdapter, type StorageAdapter } from "./storage-adapter";
import { createSyncAdapter, type SyncAdapter } from "./sync-adapter";

/**
 * Combined adapters for state management
 */
export interface StateAdapters {
  storage: StorageAdapter;
  sync: SyncAdapter;
}

/**
 * Options for adapter creation
 */
export interface AdapterOptions {
  /**
   * Force a specific context (bypasses auto-detection)
   */
  context?: "chrome-extension" | "web-app" | "node" | "test";

  /**
   * Custom storage adapter
   */
  storage?: StorageAdapter;

  /**
   * Custom sync adapter
   */
  sync?: SyncAdapter;

  /**
   * For web apps: force single-tab mode (no sync)
   */
  singleTab?: boolean;

  /**
   * Custom BroadcastChannel name for web app sync
   */
  channelName?: string;
}

/**
 * Automatically create appropriate storage and sync adapters
 * based on the execution context
 *
 * Detection order:
 * 1. Chrome extension → ChromeStorage + ChromeRuntime sync
 * 2. Web app (multi-tab) → IndexedDB + BroadcastChannel sync
 * 3. Web app (single-tab) → IndexedDB + NoOp sync
 * 4. Node.js/test → Memory storage + NoOp sync
 *
 * @example
 * ```typescript
 * // Automatic detection
 * const adapters = createStateAdapters();
 *
 * // Force single-tab mode
 * const adapters = createStateAdapters({ singleTab: true });
 *
 * // Custom adapters
 * const adapters = createStateAdapters({
 *   storage: new CustomStorageAdapter(),
 *   sync: new CustomSyncAdapter()
 * });
 * ```
 */
export function createStateAdapters(options: AdapterOptions = {}): StateAdapters {
  // Use custom adapters if provided
  if (options.storage && options.sync) {
    return {
      storage: options.storage,
      sync: options.sync,
    };
  }

  // Create storage adapter
  const storage = options.storage || createStorageAdapter();

  // Create sync adapter
  let sync: SyncAdapter;

  if (options.sync) {
    sync = options.sync;
  } else if (options.singleTab) {
    // Force no sync for single-tab mode
    const { NoOpSyncAdapter } = require("./sync-adapter");
    sync = new NoOpSyncAdapter();
  } else {
    // Auto-detect sync mechanism
    sync = createSyncAdapter();
  }

  return { storage, sync };
}

/**
 * Create adapters for Chrome extension contexts
 */
export function createChromeAdapters(): StateAdapters {
  const { ChromeStorageAdapter } = require("./storage-adapter");
  const { ChromeRuntimeSyncAdapter } = require("./sync-adapter");

  return {
    storage: new ChromeStorageAdapter(),
    sync: new ChromeRuntimeSyncAdapter(),
  };
}

/**
 * Create adapters for web apps / PWAs
 */
export function createWebAdapters(
  options: { singleTab?: boolean; channelName?: string; dbName?: string } = {}
): StateAdapters {
  const { IndexedDBAdapter } = require("./storage-adapter");
  const { BroadcastChannelSyncAdapter, NoOpSyncAdapter } = require("./sync-adapter");

  const storage = new IndexedDBAdapter(options.dbName);

  const sync = options.singleTab
    ? new NoOpSyncAdapter()
    : new BroadcastChannelSyncAdapter(options.channelName);

  return { storage, sync };
}

/**
 * Create adapters for Node.js / server contexts
 */
export function createNodeAdapters(): StateAdapters {
  const { MemoryStorageAdapter } = require("./storage-adapter");
  const { NoOpSyncAdapter } = require("./sync-adapter");

  return {
    storage: new MemoryStorageAdapter(),
    sync: new NoOpSyncAdapter(),
  };
}

/**
 * Create adapters for testing
 */
export function createMockAdapters(): StateAdapters {
  const { MemoryStorageAdapter } = require("./storage-adapter");
  const { NoOpSyncAdapter } = require("./sync-adapter");

  return {
    storage: new MemoryStorageAdapter(),
    sync: new NoOpSyncAdapter(),
  };
}
