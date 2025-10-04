// Chrome storage adapter implementation

import type { StorageAdapter, StorageChanges } from "../storage.adapter";

export class ChromeStorageAdapter implements StorageAdapter {
  async get<T = Record<string, unknown>>(keys: string | string[] | null): Promise<T> {
    return (await chrome.storage.local.get(keys)) as T;
  }

  async set(items: Record<string, unknown>): Promise<void> {
    await chrome.storage.local.set(items);
  }

  async remove(keys: string | string[]): Promise<void> {
    await chrome.storage.local.remove(keys);
  }

  async clear(): Promise<void> {
    await chrome.storage.local.clear();
  }

  onChanged(callback: (changes: StorageChanges, areaName: string) => void): void {
    chrome.storage.onChanged.addListener((changes, areaName) => {
      const mappedChanges: StorageChanges = {};
      for (const [key, change] of Object.entries(changes)) {
        mappedChanges[key] = {
          oldValue: change.oldValue,
          newValue: change.newValue,
        };
      }
      callback(mappedChanges, areaName);
    });
  }
}
