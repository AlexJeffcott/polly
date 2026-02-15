// Adapter factory and exports

import type { Context } from "../types/messages";
import { ChromeContextMenusAdapter } from "./chrome/context-menus.chrome";
import { ChromeOffscreenAdapter } from "./chrome/offscreen.chrome";
import { ChromeRuntimeAdapter } from "./chrome/runtime.chrome";
import { ChromeStorageAdapter } from "./chrome/storage.chrome";
import { ChromeTabsAdapter } from "./chrome/tabs.chrome";
import { ChromeWindowAdapter } from "./chrome/window.chrome";
import type { ContextMenusAdapter } from "./context-menus.adapter";
import type { FetchAdapter } from "./fetch.adapter";
import { BrowserFetchAdapter } from "./fetch.adapter";
import type { LoggerAdapter } from "./logger.adapter";
import { MessageLoggerAdapter } from "./logger.adapter";
import type { OffscreenAdapter } from "./offscreen.adapter";
import type { RuntimeAdapter } from "./runtime.adapter";
import type { StorageAdapter } from "./storage.adapter";
import type { TabsAdapter } from "./tabs.adapter";
import type { WindowAdapter } from "./window.adapter";

export interface ExtensionAdapters {
  runtime: RuntimeAdapter;
  storage: StorageAdapter;
  tabs: TabsAdapter;
  window: WindowAdapter;
  offscreen: OffscreenAdapter;
  contextMenus: ContextMenusAdapter;
  fetch: FetchAdapter;
  logger: LoggerAdapter;
}

export interface CreateChromeAdaptersOptions {
  consoleMirror?: boolean; // Mirror logs to console for development
}

/**
 * Create Chrome-specific adapters with context
 */
export function createChromeAdapters(
  context: Context,
  options?: CreateChromeAdaptersOptions
): ExtensionAdapters {
  const runtime = new ChromeRuntimeAdapter();

  return {
    runtime,
    storage: new ChromeStorageAdapter(),
    tabs: new ChromeTabsAdapter(),
    window: new ChromeWindowAdapter(),
    offscreen: new ChromeOffscreenAdapter(),
    contextMenus: new ChromeContextMenusAdapter(),
    fetch: new BrowserFetchAdapter(),
    logger: new MessageLoggerAdapter(runtime, context, {
      ...(options?.consoleMirror !== undefined && { consoleMirror: options.consoleMirror }),
      fallbackToConsole: true,
    }),
  };
}

export {
  type AdapterOptions,
  createChromeAdapters as createChromeStateAdapters,
  createMockAdapters,
  createNodeAdapters,
  createStateAdapters,
  createWebAdapters,
  type StateAdapters,
} from "../lib/adapter-factory";
// Re-export state management adapters
// Note: Avoid duplicate StorageAdapter export - use named exports to prevent conflicts
export {
  ChromeStorageAdapter as UniversalChromeStorageAdapter,
  createStorageAdapter,
  IndexedDBAdapter,
  MemoryStorageAdapter,
  type StorageAdapter as UniversalStorageAdapter,
} from "../lib/storage-adapter";
export {
  BroadcastChannelSyncAdapter,
  ChromeRuntimeSyncAdapter,
  createSyncAdapter,
  NoOpSyncAdapter,
  type StateSyncMessage,
  type SyncAdapter,
} from "../lib/sync-adapter";
export * from "./context-menus.adapter";
export * from "./fetch.adapter";
export * from "./logger.adapter";
export * from "./offscreen.adapter";
// Re-export types
export * from "./runtime.adapter";
export * from "./storage.adapter";
export * from "./tabs.adapter";
export * from "./window.adapter";
