// Storage adapters for different execution contexts
// Automatically chooses the right storage mechanism based on environment

import { cachedOpen, runRequest, runTx } from "./idb-helpers";

/**
 * Universal storage adapter interface
 */
export interface StorageAdapter {
  get<T = unknown>(keys: string[]): Promise<Record<string, T>>;
  set(items: Record<string, unknown>): Promise<void>;
  remove(keys: string[]): Promise<void>;
}

/**
 * IndexedDB adapter for web apps
 */
export class IndexedDBAdapter implements StorageAdapter {
  private readonly dbName: string;
  private readonly storeName = "state";
  private readonly dbRef: { promise: Promise<IDBDatabase> | null } = { promise: null };

  constructor(dbName = "polly-state") {
    this.dbName = dbName;
  }

  private getDB(): Promise<IDBDatabase> {
    return cachedOpen(this.dbRef, {
      name: this.dbName,
      version: 1,
      upgrade: (db) => {
        if (!db.objectStoreNames.contains(this.storeName)) {
          db.createObjectStore(this.storeName);
        }
      },
    });
  }

  async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
    try {
      const db = await this.getDB();
      const tx = db.transaction(this.storeName, "readonly");
      const store = tx.objectStore(this.storeName);
      const pairs = await Promise.all(
        keys.map(async (key) => [key, await runRequest(store.get(key))] as const)
      );
      const result: Record<string, T> = {};
      for (const [key, value] of pairs) {
        if (value !== undefined) result[key] = value as T;
      }
      return result;
    } catch (error) {
      console.warn("[Polly] IndexedDB get failed:", error);
      return {};
    }
  }

  async set(items: Record<string, unknown>): Promise<void> {
    try {
      const db = await this.getDB();
      await runTx(db, this.storeName, "readwrite", (store) => {
        for (const [key, value] of Object.entries(items)) {
          store.put(value, key);
        }
      });
    } catch (error) {
      console.warn("[Polly] IndexedDB set failed:", error);
    }
  }

  async remove(keys: string[]): Promise<void> {
    try {
      const db = await this.getDB();
      await runTx(db, this.storeName, "readwrite", (store) => {
        for (const key of keys) store.delete(key);
      });
    } catch (error) {
      console.warn("[Polly] IndexedDB remove failed:", error);
    }
  }
}

/**
 * Chrome storage adapter for extensions
 */
export class ChromeStorageAdapter implements StorageAdapter {
  async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
    if (typeof chrome === "undefined" || !chrome.storage) {
      return {};
    }

    try {
      return (await chrome.storage.local.get(keys)) as unknown as Record<string, T>;
    } catch (error) {
      console.warn("[Polly] Chrome storage get failed:", error);
      return {};
    }
  }

  async set(items: Record<string, unknown>): Promise<void> {
    if (typeof chrome === "undefined" || !chrome.storage) {
      return;
    }

    try {
      await chrome.storage.local.set(items);
    } catch (error) {
      console.warn("[Polly] Chrome storage set failed:", error);
    }
  }

  async remove(keys: string[]): Promise<void> {
    if (typeof chrome === "undefined" || !chrome.storage) {
      return;
    }

    try {
      await chrome.storage.local.remove(keys);
    } catch (error) {
      console.warn("[Polly] Chrome storage remove failed:", error);
    }
  }
}

/**
 * In-memory adapter (no persistence) for testing or server contexts
 */
export class MemoryStorageAdapter implements StorageAdapter {
  private storage = new Map<string, unknown>();

  async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
    const result: Record<string, T> = {};
    for (const key of keys) {
      const value = this.storage.get(key);
      if (value !== undefined) {
        result[key] = value as unknown as T;
      }
    }
    return result;
  }

  async set(items: Record<string, unknown>): Promise<void> {
    for (const [key, value] of Object.entries(items)) {
      this.storage.set(key, value);
    }
  }

  async remove(keys: string[]): Promise<void> {
    for (const key of keys) {
      this.storage.delete(key);
    }
  }
}

/**
 * Detect execution context and return appropriate storage adapter
 */
export function createStorageAdapter(): StorageAdapter {
  // Chrome extension context
  if (typeof chrome !== "undefined" && chrome.storage && chrome.runtime) {
    return new ChromeStorageAdapter();
  }

  // Web app context (has IndexedDB)
  if (typeof indexedDB !== "undefined") {
    return new IndexedDBAdapter();
  }

  // Server/test context (no persistent storage available)
  return new MemoryStorageAdapter();
}
