import type { StorageAdapter, StorageChanges } from "@/shared/adapters/storage.adapter";

export interface MockStorageArea extends StorageAdapter {
  _data: Map<string, unknown>;
}

export function createMockStorageArea(): MockStorageArea {
  const data = new Map<string, unknown>();

  return {
    get: async <T = Record<string, unknown>>(
      keys?: string | string[] | Record<string, unknown> | null
      // biome-ignore lint/complexity/noExcessiveCognitiveComplexity: Mock storage needs to handle multiple key types
    ): Promise<T> => {
      if (!keys) {
        return Object.fromEntries(data) as T;
      }
      if (typeof keys === "string") {
        return (data.has(keys) ? { [keys]: data.get(keys) } : {}) as T;
      }
      if (Array.isArray(keys)) {
        const result: Record<string, unknown> = {};
        for (const key of keys) {
          if (data.has(key)) {
            result[key] = data.get(key);
          }
        }
        return result as T;
      }
      // Object with defaults
      const result: Record<string, unknown> = {};
      for (const [key, defaultValue] of Object.entries(keys)) {
        result[key] = data.has(key) ? data.get(key) : defaultValue;
      }
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
