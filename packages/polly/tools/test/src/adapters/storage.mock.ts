import type { StorageAdapter, StorageChanges } from "@/shared/adapters/storage.adapter";

export interface MockStorageArea extends StorageAdapter {
  _data: Map<string, unknown>;
}

export function createMockStorageArea(): MockStorageArea {
  const data = new Map<string, unknown>();

  return {
    get: async <T = Record<string, unknown>>(
      keys?: string | string[] | Record<string, unknown> | null
    ): Promise<T> => {
      // The mock erases T like chrome.storage does; the caller names the shape it stored.
      let result: unknown;
      if (!keys) {
        result = Object.fromEntries(data);
      } else if (typeof keys === "string") {
        result = data.has(keys) ? { [keys]: data.get(keys) } : {};
      } else if (Array.isArray(keys)) {
        result = Object.fromEntries(
          keys.filter((key) => data.has(key)).map((key) => [key, data.get(key)])
        );
      } else {
        // Object with defaults
        result = Object.fromEntries(
          Object.entries(keys).map(([key, fallback]) => [
            key,
            data.has(key) ? data.get(key) : fallback,
          ])
        );
      }
      // cast: chrome.storage returns what was stored; the caller's T names that shape
      return result as T;
    },
    set: async (items) => {
      for (const [key, value] of Object.entries(items)) {
        data.set(key, value);
      }
    },
    remove: async (keys) => {
      const keyArray = Array.isArray(keys) ? keys : [keys];
      for (const key of keyArray) {
        data.delete(key);
      }
    },
    clear: async () => {
      data.clear();
    },
    onChanged: (_callback: (changes: StorageChanges, areaName: string) => void) => {
      // Mock implementation - not needed for current tests
    },
    _data: data,
  };
}
