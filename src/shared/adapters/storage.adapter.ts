// Storage adapter interface (wraps chrome.storage)

export interface StorageAdapter {
  /**
   * Get items from storage
   * @param keys - String, array of strings, object with defaults, or null for all items
   */
  get<T = Record<string, unknown>>(
    keys?: string | string[] | Record<string, unknown> | null
  ): Promise<T>;

  /**
   * Set items in storage
   */
  set(items: Record<string, unknown>): Promise<void>;

  /**
   * Remove items from storage
   */
  remove(keys: string | string[]): Promise<void>;

  /**
   * Clear all storage
   */
  clear(): Promise<void>;

  /**
   * Listen for storage changes
   */
  onChanged(callback: (changes: StorageChanges, areaName: string) => void): void;
}

export interface StorageChanges {
  [key: string]: {
    oldValue?: unknown;
    newValue?: unknown;
  };
}
