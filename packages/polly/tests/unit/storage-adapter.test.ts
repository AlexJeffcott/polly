/**
 * Tests for storage-adapter.ts — the three universal-storage backends
 * (Memory / Chrome / IndexedDB) plus the `createStorageAdapter` context
 * detector.
 *
 * bun:test has no `indexedDB` and no `chrome` global, so both are faked
 * here: a tiny in-memory IndexedDB (open → upgrade → transaction → store
 * get/put/delete) installed on `globalThis.indexedDB` drives the real
 * `idb-helpers` path the `IndexedDBAdapter` runs through, and a captured
 * `chrome.storage.local` mock drives the `ChromeStorageAdapter`. Each
 * suite saves and restores the globals so the detector tests see a clean
 * environment.
 */

import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import {
  ChromeStorageAdapter,
  createStorageAdapter,
  IndexedDBAdapter,
  MemoryStorageAdapter,
} from "@/shared/lib/storage-adapter";

// ---------------------------------------------------------------------------
// In-memory IndexedDB fake — only the surface idb-helpers touches.
// ---------------------------------------------------------------------------

class FakeRequest<T> {
  onsuccess: (() => void) | null = null;
  onerror: (() => void) | null = null;
  result: T | undefined;
  error: DOMException | null = null;

  fireSuccess(result: T): void {
    this.result = result;
    queueMicrotask(() => this.onsuccess?.());
  }
}

class FakeStore {
  constructor(private readonly map: Map<string, unknown>) {}

  get(key: string): FakeRequest<unknown> {
    const request = new FakeRequest<unknown>();
    request.fireSuccess(this.map.get(key));
    return request;
  }

  put(value: unknown, key: string): FakeRequest<undefined> {
    this.map.set(key, value);
    const request = new FakeRequest<undefined>();
    request.fireSuccess(undefined);
    return request;
  }

  delete(key: string): FakeRequest<undefined> {
    this.map.delete(key);
    const request = new FakeRequest<undefined>();
    request.fireSuccess(undefined);
    return request;
  }
}

class FakeTransaction {
  oncomplete: (() => void) | null = null;
  onerror: (() => void) | null = null;
  onabort: (() => void) | null = null;
  error: DOMException | null = null;
  private aborted = false;

  constructor(private readonly store: FakeStore) {
    // Resolve after the synchronous executor body (which assigns
    // oncomplete and runs the mutating callback) has finished.
    queueMicrotask(() => {
      if (!this.aborted) this.oncomplete?.();
    });
  }

  objectStore(): FakeStore {
    return this.store;
  }

  abort(): void {
    this.aborted = true;
    queueMicrotask(() => this.onabort?.());
  }
}

class FakeDB {
  private readonly stores = new Map<string, Map<string, unknown>>();
  readonly objectStoreNames = {
    contains: (name: string): boolean => this.stores.has(name),
  };

  createObjectStore(name: string): void {
    this.stores.set(name, new Map());
  }

  transaction(name: string, mode: string): FakeTransaction {
    // Match real IndexedDB's strictness so the source's choices are
    // observable: an invalid mode and an unknown store both throw. This is
    // what makes `transaction(store, "readonly"/"readwrite")` and the
    // upgrade's `createObjectStore` carry mutation weight.
    if (mode !== "readonly" && mode !== "readwrite") {
      throw new Error(`FakeDB: invalid transaction mode '${mode}'`);
    }
    const store = this.stores.get(name);
    if (!store) {
      throw new Error(`FakeDB: object store '${name}' was never created`);
    }
    return new FakeTransaction(new FakeStore(store));
  }
}

interface FakeOpenRequest {
  onsuccess: (() => void) | null;
  onerror: (() => void) | null;
  onupgradeneeded: ((event: { target: FakeOpenRequest }) => void) | null;
  onblocked: (() => void) | null;
  result: FakeDB | null;
  error: DOMException | null;
}

interface FakeIndexedDB {
  open: (name: string, version: number) => FakeOpenRequest;
  /** Names passed to `open`, in call order — lets a test pin the dbName. */
  openedNames: string[];
}

function makeFakeIndexedDB(): FakeIndexedDB {
  const databases = new Map<string, FakeDB>();
  const openedNames: string[] = [];
  return {
    openedNames,
    open(name: string): FakeOpenRequest {
      openedNames.push(name);
      const request: FakeOpenRequest = {
        onsuccess: null,
        onerror: null,
        onupgradeneeded: null,
        onblocked: null,
        result: null,
        error: null,
      };
      queueMicrotask(() => {
        let db = databases.get(name);
        const isNew = !db;
        if (!db) {
          db = new FakeDB();
          databases.set(name, db);
        }
        request.result = db;
        if (isNew) request.onupgradeneeded?.({ target: request });
        request.onsuccess?.();
      });
      return request;
    },
  };
}

type GlobalWithIDB = { indexedDB?: unknown };

function setIndexedDB(value: unknown): void {
  (globalThis as unknown as GlobalWithIDB).indexedDB = value;
}

// ---------------------------------------------------------------------------
// MemoryStorageAdapter
// ---------------------------------------------------------------------------

describe("MemoryStorageAdapter", () => {
  test("set then get round-trips values by key", async () => {
    const adapter = new MemoryStorageAdapter();
    await adapter.set({ a: 1, b: "two" });
    expect(await adapter.get(["a", "b"])).toEqual({ a: 1, b: "two" });
  });

  test("get omits keys that were never set", async () => {
    const adapter = new MemoryStorageAdapter();
    await adapter.set({ a: 1 });
    expect(await adapter.get(["a", "missing"])).toEqual({ a: 1 });
  });

  test("get omits keys whose stored value is undefined", async () => {
    const adapter = new MemoryStorageAdapter();
    await adapter.set({ a: undefined });
    // Object.keys, not toEqual — bun's toEqual treats {a: undefined} as {},
    // so the `if (value !== undefined)` filter being defeated would slip past.
    expect(Object.keys(await adapter.get(["a"]))).toEqual([]);
  });

  test("get returns an empty object when nothing matches", async () => {
    const adapter = new MemoryStorageAdapter();
    expect(await adapter.get(["nope"])).toEqual({});
  });

  test("remove deletes only the listed keys", async () => {
    const adapter = new MemoryStorageAdapter();
    await adapter.set({ a: 1, b: 2, c: 3 });
    await adapter.remove(["a", "c"]);
    expect(await adapter.get(["a", "b", "c"])).toEqual({ b: 2 });
  });
});

// ---------------------------------------------------------------------------
// ChromeStorageAdapter
// ---------------------------------------------------------------------------

interface ChromeMock {
  storage: {
    local: {
      get: (keys: string[]) => Promise<Record<string, unknown>>;
      set: (items: Record<string, unknown>) => Promise<void>;
      remove: (keys: string[]) => Promise<void>;
    };
  };
}

type GlobalWithChrome = { chrome?: unknown };

function setChrome(value: unknown): void {
  (globalThis as unknown as GlobalWithChrome).chrome = value;
}

function deleteChrome(): void {
  delete (globalThis as unknown as GlobalWithChrome).chrome;
}

describe("ChromeStorageAdapter", () => {
  let hadChrome = false;
  let savedChrome: unknown;
  let warnings: unknown[][];
  const realWarn = console.warn;

  beforeEach(() => {
    hadChrome = "chrome" in globalThis;
    savedChrome = (globalThis as unknown as GlobalWithChrome).chrome;
    warnings = [];
    console.warn = (...args: unknown[]) => warnings.push(args);
  });

  afterEach(() => {
    console.warn = realWarn;
    if (hadChrome) setChrome(savedChrome);
    else deleteChrome();
  });

  function installChrome(): {
    sets: Record<string, unknown>[];
    removes: string[][];
    store: Record<string, unknown>;
  } {
    const sets: Record<string, unknown>[] = [];
    const removes: string[][] = [];
    const store: Record<string, unknown> = { x: 1, y: 2 };
    const mock: ChromeMock = {
      storage: {
        local: {
          get: async (keys) => {
            const out: Record<string, unknown> = {};
            for (const key of keys) if (key in store) out[key] = store[key];
            return out;
          },
          set: async (items) => {
            sets.push(items);
          },
          remove: async (keys) => {
            removes.push(keys);
          },
        },
      },
    };
    setChrome(mock);
    return { sets, removes, store };
  }

  test("get reads through chrome.storage.local.get", async () => {
    installChrome();
    const adapter = new ChromeStorageAdapter();
    expect(await adapter.get(["x", "y"])).toEqual({ x: 1, y: 2 });
  });

  test("set writes through chrome.storage.local.set", async () => {
    const { sets } = installChrome();
    const adapter = new ChromeStorageAdapter();
    await adapter.set({ z: 9 });
    expect(sets).toEqual([{ z: 9 }]);
  });

  test("remove deletes through chrome.storage.local.remove", async () => {
    const { removes } = installChrome();
    const adapter = new ChromeStorageAdapter();
    await adapter.remove(["x"]);
    expect(removes).toEqual([["x"]]);
  });

  // The guard `typeof chrome === "undefined" || !chrome.storage` is exercised
  // from BOTH arms for each method, each asserting the result AND that no warn
  // fired. The `deleteChrome` arm makes the first comparison decide (so the
  // `"undefined"` string and the `false || …` short-circuit matter); the
  // empty-`chrome` arm makes `!chrome.storage` decide. Any guard mutant either
  // throws (caught by the resolve assertion) or falls through to the catch and
  // warns (caught by the no-warn assertion).
  test("get short-circuits without warning when chrome is absent", async () => {
    deleteChrome();
    expect(await new ChromeStorageAdapter().get(["x"])).toEqual({});
    expect(warnings).toEqual([]);
  });

  test("get short-circuits without warning when chrome.storage is missing", async () => {
    setChrome({});
    expect(await new ChromeStorageAdapter().get(["x"])).toEqual({});
    expect(warnings).toEqual([]);
  });

  test("set short-circuits without warning when chrome is absent", async () => {
    deleteChrome();
    await expect(new ChromeStorageAdapter().set({ z: 1 })).resolves.toBeUndefined();
    expect(warnings).toEqual([]);
  });

  test("set short-circuits without warning when chrome.storage is missing", async () => {
    setChrome({});
    await expect(new ChromeStorageAdapter().set({ z: 1 })).resolves.toBeUndefined();
    expect(warnings).toEqual([]);
  });

  test("remove short-circuits without warning when chrome is absent", async () => {
    deleteChrome();
    await expect(new ChromeStorageAdapter().remove(["x"])).resolves.toBeUndefined();
    expect(warnings).toEqual([]);
  });

  test("remove short-circuits without warning when chrome.storage is missing", async () => {
    setChrome({});
    await expect(new ChromeStorageAdapter().remove(["x"])).resolves.toBeUndefined();
    expect(warnings).toEqual([]);
  });

  test("get warns and returns {} when chrome.storage.local.get rejects", async () => {
    setChrome({
      storage: {
        local: {
          get: async () => {
            throw new Error("boom");
          },
        },
      },
    });
    const adapter = new ChromeStorageAdapter();
    expect(await adapter.get(["x"])).toEqual({});
    expect(warnings.some((w) => String(w[0]).includes("Chrome storage get failed"))).toBe(true);
  });

  test("set warns when chrome.storage.local.set rejects", async () => {
    setChrome({
      storage: {
        local: {
          set: async () => {
            throw new Error("boom");
          },
        },
      },
    });
    const adapter = new ChromeStorageAdapter();
    await adapter.set({ z: 1 });
    expect(warnings.some((w) => String(w[0]).includes("Chrome storage set failed"))).toBe(true);
  });

  test("remove warns when chrome.storage.local.remove rejects", async () => {
    setChrome({
      storage: {
        local: {
          remove: async () => {
            throw new Error("boom");
          },
        },
      },
    });
    const adapter = new ChromeStorageAdapter();
    await adapter.remove(["x"]);
    expect(warnings.some((w) => String(w[0]).includes("Chrome storage remove failed"))).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// IndexedDBAdapter (driven against the in-memory IDB fake)
// ---------------------------------------------------------------------------

describe("IndexedDBAdapter", () => {
  let hadIDB = false;
  let savedIDB: unknown;
  let warnings: unknown[][];
  const realWarn = console.warn;

  beforeEach(() => {
    hadIDB = "indexedDB" in globalThis;
    savedIDB = (globalThis as unknown as GlobalWithIDB).indexedDB;
    warnings = [];
    console.warn = (...args: unknown[]) => warnings.push(args);
    setIndexedDB(makeFakeIndexedDB());
  });

  afterEach(() => {
    console.warn = realWarn;
    if (hadIDB) setIndexedDB(savedIDB);
    else delete (globalThis as unknown as GlobalWithIDB).indexedDB;
  });

  test("set then get round-trips values", async () => {
    const adapter = new IndexedDBAdapter("polly-test-rt");
    await adapter.set({ a: 1, b: "two" });
    expect(await adapter.get(["a", "b"])).toEqual({ a: 1, b: "two" });
  });

  test("get omits keys with no stored value", async () => {
    const adapter = new IndexedDBAdapter("polly-test-miss");
    await adapter.set({ a: 1 });
    const result = await adapter.get(["a", "absent"]);
    expect(result).toEqual({ a: 1 });
    // Object.keys, not just toEqual — defeating the `value !== undefined`
    // filter would add an `absent: undefined` entry toEqual ignores.
    expect(Object.keys(result)).toEqual(["a"]);
  });

  test("remove deletes the listed keys only", async () => {
    const adapter = new IndexedDBAdapter("polly-test-rm");
    await adapter.set({ a: 1, b: 2 });
    await adapter.remove(["a"]);
    expect(await adapter.get(["a", "b"])).toEqual({ b: 2 });
  });

  test("defaults the database name to 'polly-state'", async () => {
    const fake = makeFakeIndexedDB();
    setIndexedDB(fake);
    await new IndexedDBAdapter().set({ a: 1 });
    expect(fake.openedNames).toEqual(["polly-state"]);
  });

  test("honours an explicit database name", async () => {
    const fake = makeFakeIndexedDB();
    setIndexedDB(fake);
    await new IndexedDBAdapter("custom-db").set({ a: 1 });
    expect(fake.openedNames).toEqual(["custom-db"]);
  });

  test("reuses one database across operations on the same instance", async () => {
    const adapter = new IndexedDBAdapter("polly-test-reuse");
    await adapter.set({ a: 1 });
    await adapter.set({ b: 2 });
    expect(await adapter.get(["a", "b"])).toEqual({ a: 1, b: 2 });
  });

  test("get warns and returns {} when the database cannot be opened", async () => {
    setIndexedDB(undefined);
    const adapter = new IndexedDBAdapter("polly-test-fail");
    expect(await adapter.get(["a"])).toEqual({});
    expect(warnings.some((w) => String(w[0]).includes("IndexedDB get failed"))).toBe(true);
  });

  test("set warns when the database cannot be opened", async () => {
    setIndexedDB(undefined);
    const adapter = new IndexedDBAdapter("polly-test-fail-set");
    await adapter.set({ a: 1 });
    expect(warnings.some((w) => String(w[0]).includes("IndexedDB set failed"))).toBe(true);
  });

  test("remove warns when the database cannot be opened", async () => {
    setIndexedDB(undefined);
    const adapter = new IndexedDBAdapter("polly-test-fail-rm");
    await adapter.remove(["a"]);
    expect(warnings.some((w) => String(w[0]).includes("IndexedDB remove failed"))).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// createStorageAdapter — context detection
// ---------------------------------------------------------------------------

describe("createStorageAdapter", () => {
  let hadChrome = false;
  let savedChrome: unknown;
  let hadIDB = false;
  let savedIDB: unknown;

  beforeEach(() => {
    hadChrome = "chrome" in globalThis;
    savedChrome = (globalThis as unknown as GlobalWithChrome).chrome;
    hadIDB = "indexedDB" in globalThis;
    savedIDB = (globalThis as unknown as GlobalWithIDB).indexedDB;
  });

  afterEach(() => {
    if (hadChrome) setChrome(savedChrome);
    else deleteChrome();
    if (hadIDB) setIndexedDB(savedIDB);
    else delete (globalThis as unknown as GlobalWithIDB).indexedDB;
  });

  test("returns a ChromeStorageAdapter when chrome.storage and chrome.runtime exist", () => {
    setChrome({ storage: { local: {} }, runtime: {} });
    setIndexedDB(makeFakeIndexedDB());
    expect(createStorageAdapter()).toBeInstanceOf(ChromeStorageAdapter);
  });

  test("falls through to IndexedDB when chrome lacks runtime", () => {
    setChrome({ storage: { local: {} } });
    setIndexedDB(makeFakeIndexedDB());
    expect(createStorageAdapter()).toBeInstanceOf(IndexedDBAdapter);
  });

  test("falls through to IndexedDB when chrome lacks storage", () => {
    setChrome({ runtime: {} });
    setIndexedDB(makeFakeIndexedDB());
    expect(createStorageAdapter()).toBeInstanceOf(IndexedDBAdapter);
  });

  test("returns an IndexedDBAdapter in a web context with no chrome", () => {
    deleteChrome();
    setIndexedDB(makeFakeIndexedDB());
    expect(createStorageAdapter()).toBeInstanceOf(IndexedDBAdapter);
  });

  test("falls back to MemoryStorageAdapter when neither chrome nor indexedDB exists", () => {
    deleteChrome();
    delete (globalThis as unknown as GlobalWithIDB).indexedDB;
    expect(createStorageAdapter()).toBeInstanceOf(MemoryStorageAdapter);
  });
});
