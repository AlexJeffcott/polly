// Chrome tabs adapter implementation

import type { TabsAdapter } from "../tabs.adapter";

export class ChromeTabsAdapter implements TabsAdapter {
  async query(queryInfo: chrome.tabs.QueryInfo): Promise<chrome.tabs.Tab[]> {
    return chrome.tabs.query(queryInfo);
  }

  async get(tabId: number): Promise<chrome.tabs.Tab> {
    return chrome.tabs.get(tabId);
  }

  async sendMessage(tabId: number, message: unknown): Promise<unknown> {
    return chrome.tabs.sendMessage(tabId, message);
  }

  async reload(tabId: number, reloadProperties?: { bypassCache?: boolean }): Promise<void> {
    await chrome.tabs.reload(tabId, reloadProperties);
  }

  onRemoved(callback: (tabId: number, removeInfo: chrome.tabs.TabRemoveInfo) => void): void {
    chrome.tabs.onRemoved.addListener(callback);
  }

  onUpdated(
    callback: (tabId: number, changeInfo: chrome.tabs.TabChangeInfo, tab: chrome.tabs.Tab) => void
  ): void {
    chrome.tabs.onUpdated.addListener(callback);
  }

  onActivated(callback: (activeInfo: { tabId: number; windowId: number }) => void): void {
    chrome.tabs.onActivated.addListener(callback);
  }

  async create(createProperties: chrome.tabs.CreateProperties): Promise<chrome.tabs.Tab> {
    return chrome.tabs.create(createProperties);
  }
}
