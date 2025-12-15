import type { ContextMenusAdapter } from "@/shared/adapters/context-menus.adapter";

export interface MockContextMenus extends ContextMenusAdapter {
  _menus: Map<string, chrome.contextMenus.CreateProperties>;
}

export function createMockContextMenus(): MockContextMenus {
  const menus = new Map<string, chrome.contextMenus.CreateProperties>();

  return {
    create: async (createProperties: chrome.contextMenus.CreateProperties): Promise<void> => {
      if (createProperties.id) {
        menus.set(createProperties.id, createProperties);
      }
    },
    update: async (
      _id: string,
      _updateProperties: chrome.contextMenus.UpdateProperties
    ): Promise<void> => {
      // Mock implementation
    },
    remove: async (_id: string): Promise<void> => {
      // Mock implementation
    },
    removeAll: async (): Promise<void> => {
      // Mock implementation
    },
    onClicked: (
      _callback: (info: chrome.contextMenus.OnClickData, tab?: chrome.tabs.Tab) => void
    ): void => {
      // Mock implementation
    },
    _menus: menus,
  };
}
