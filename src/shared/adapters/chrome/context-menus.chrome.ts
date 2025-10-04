// Chrome context menus adapter implementation

import type { ContextMenusAdapter } from "../context-menus.adapter";

export class ChromeContextMenusAdapter implements ContextMenusAdapter {
  async create(createProperties: chrome.contextMenus.CreateProperties): Promise<void> {
    return new Promise((resolve, reject) => {
      chrome.contextMenus.create(createProperties, () => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message));
        } else {
          resolve();
        }
      });
    });
  }

  async update(id: string, updateProperties: chrome.contextMenus.UpdateProperties): Promise<void> {
    await chrome.contextMenus.update(id, updateProperties);
  }

  async remove(id: string): Promise<void> {
    await chrome.contextMenus.remove(id);
  }

  async removeAll(): Promise<void> {
    await chrome.contextMenus.removeAll();
  }

  onClicked(
    callback: (info: chrome.contextMenus.OnClickData, tab?: chrome.tabs.Tab) => void
  ): void {
    chrome.contextMenus.onClicked.addListener(callback);
  }
}
