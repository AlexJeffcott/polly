// Storage adapters for different execution contexts
// Automatically chooses the right storage mechanism based on environment

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
  private dbName: string;
  private storeName = "state";
  private dbPromise: Promise<IDBDatabase> | null = null;

  constructor(dbName = "polly-state") {
    this.dbName = dbName;
  }

  private getDB(): Promise<IDBDatabase> {
    if (this.dbPromise) return this.dbPromise;

    this.dbPromise = new Promise((resolve, reject) => {
      const request = indexedDB.open(this.dbName, 1);

      request.onerror = () => reject(request.error);
      request.onsuccess = () => resolve(request.result);

      request.onupgradeneeded = (event) => {
        const db = (event.target as IDBOpenDBRequest).result;
        if (!db.objectStoreNames.contains(this.storeName)) {
          db.createObjectStore(this.storeName);
        }
      };
    });

    return this.dbPromise;
  }

  async get<T = unknown>(keys: string[]): Promise<Record<string, T>> {
    try {
      const db = await this.getDB();
      const result: Record<string, T> = {};

      await Promise.all(
        keys.map(
          (key) =>
            new Promise<void>((resolve, reject) => {
              const transaction = db.transaction([this.storeName], "readonly");
              const store = transaction.objectStore(this.storeName);
              const request = store.get(key);

              request.onerror = () => reject(request.error);
              request.onsuccess = () => {
                if (request.result !== undefined) {
                  result[key] = request.result as T;
                }
                resolve();
              };
            })
        )
      );

      return result;
    } catch (error) {
      console.warn("[Polly] IndexedDB get failed:", error);
      return {};
    }
  }

  async set(items: Record<string, unknown>): Promise<void> {
    try {
      const db = await this.getDB();
      await Promise.all(
        Object.entries(items).map(
          ([key, value]) =>
            new Promise<void>((resolve, reject) => {
              const transaction = db.transaction([this.storeName], "readwrite");
              const store = transaction.objectStore(this.storeName);
              const request = store.put(value, key);

              request.onerror = () => reject(request.error);
              request.onsuccess = () => resolve();
            })
        )
      );
    } catch (error) {
      console.warn("[Polly] IndexedDB set failed:", error);
    }
  }

  async remove(keys: string[]): Promise<void> {
    try {
      const db = await this.getDB();
      await Promise.all(
        keys.map(
          (key) =>
            new Promise<void>((resolve, reject) => {
              const transaction = db.transaction([this.storeName], "readwrite");
              const store = transaction.objectStore(this.storeName);
              const request = store.delete(key);

              request.onerror = () => reject(request.error);
              request.onsuccess = () => resolve();
            })
        )
      );
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
      return (await chrome.storage.local.get(keys)) as Record<string, T>;
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
        result[key] = value as T;
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
