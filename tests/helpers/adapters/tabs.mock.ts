import type { TabsAdapter } from "@/shared/adapters/tabs.adapter";

export interface MockTabs extends TabsAdapter {
  _tabs: Map<number, chrome.tabs.Tab>;
}

export function createMockTabs(): MockTabs {
  const tabs = new Map<number, chrome.tabs.Tab>();

  return {
    query: async (queryInfo: chrome.tabs.QueryInfo): Promise<chrome.tabs.Tab[]> => {
      const results: chrome.tabs.Tab[] = [];
      for (const tab of tabs.values()) {
        let matches = true;
        if (queryInfo.active !== undefined && tab.active !== queryInfo.active) {
          matches = false;
        }
        if (queryInfo.currentWindow !== undefined) {
          matches = false;
        }
        if (matches) {
          results.push(tab);
        }
      }
      return results;
    },
    get: async (tabId: number): Promise<chrome.tabs.Tab> => {
      const tab = tabs.get(tabId);
      if (!tab) {
        throw new Error(`Tab ${tabId} not found`);
      }
      return tab;
    },
    sendMessage: async (_tabId: number, _message: unknown): Promise<unknown> => {
      return Promise.resolve({ success: true });
    },
    reload: async (
      _tabId: number,
      _reloadProperties?: { bypassCache?: boolean }
    ): Promise<void> => {
      // Mock implementation
    },
    onRemoved: (
      _callback: (tabId: number, removeInfo: chrome.tabs.TabRemoveInfo) => void
    ): void => {
      // Mock implementation - register listener
    },
    onUpdated: (
      _callback: (
        tabId: number,
        changeInfo: chrome.tabs.TabChangeInfo,
        tab: chrome.tabs.Tab
      ) => void
    ): void => {
      // Mock implementation - register listener
    },
    onActivated: (_callback: (activeInfo: { tabId: number; windowId: number }) => void): void => {
      // Mock implementation - register listener
    },
    _tabs: tabs,
  };
}
