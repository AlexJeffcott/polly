// Tabs adapter interface (wraps chrome.tabs)

export interface TabsAdapter {
  /**
   * Query tabs
   */
  query(queryInfo: chrome.tabs.QueryInfo): Promise<chrome.tabs.Tab[]>;

  /**
   * Get tab by ID
   */
  get(tabId: number): Promise<chrome.tabs.Tab>;

  /**
   * Send message to specific tab
   */
  sendMessage(tabId: number, message: unknown): Promise<unknown>;

  /**
   * Reload tab
   */
  reload(tabId: number, reloadProperties?: { bypassCache?: boolean }): Promise<void>;

  /**
   * Listen for tab removal
   */
  onRemoved(callback: (tabId: number, removeInfo: chrome.tabs.TabRemoveInfo) => void): void;

  /**
   * Listen for tab updates
   */
  onUpdated(
    callback: (tabId: number, changeInfo: chrome.tabs.TabChangeInfo, tab: chrome.tabs.Tab) => void
  ): void;

  /**
   * Listen for tab activation
   */
  onActivated(callback: (activeInfo: { tabId: number; windowId: number }) => void): void;

  /**
   * Create a new tab
   */
  create(createProperties: chrome.tabs.CreateProperties): Promise<chrome.tabs.Tab>;
}
