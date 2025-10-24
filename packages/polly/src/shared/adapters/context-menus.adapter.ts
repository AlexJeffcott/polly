// Context menus adapter interface (wraps chrome.contextMenus)

export interface ContextMenusAdapter {
  /**
   * Create context menu item
   */
  create(createProperties: chrome.contextMenus.CreateProperties): Promise<void>;

  /**
   * Update context menu item
   */
  update(id: string, updateProperties: chrome.contextMenus.UpdateProperties): Promise<void>;

  /**
   * Remove context menu item
   */
  remove(id: string): Promise<void>;

  /**
   * Remove all context menu items
   */
  removeAll(): Promise<void>;

  /**
   * Listen for context menu clicks
   */
  onClicked(callback: (info: chrome.contextMenus.OnClickData, tab?: chrome.tabs.Tab) => void): void;
}
